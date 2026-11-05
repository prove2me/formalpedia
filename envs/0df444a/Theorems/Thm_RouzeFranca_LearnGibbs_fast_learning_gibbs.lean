-- Prove2me | Theorems.Thm_RouzeFranca_LearnGibbs_fast_learning_gibbs
-- name    : RouzeFranca.LearnGibbs.fast_learning_gibbs
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:48:42.044022+00:00
-- url     : https://prove2.me/theorems/41a9bc1b-f881-4da0-8f95-36085b50b140
-- title:
--   Theorem C.1 (Fast learning of Gibbs states) — under TC, $O(4^k\alpha^{-1}\epsilon^{-2}\beta\log(m/\delta)\min\{\frac{m\beta}{Ln},\frac{m^2}{\alpha n^2\epsilon^2}\})$ copies suffice
-- statement:
--   There is a universal constant $C>0$ with the following property. Let $E_1,\dots,E_m$ ($m\ge1$) be linearly independent, Hermitian, $k$-local observables on $n\ge1$ qubits with $\|E_i\|_\infty\le1$. Let $\beta,\alpha,L,\epsilon>0$ and $\delta\in(0,1)$, and assume that $\mu\mapsto\log\mathcal Z(\mu)$ is $L$-strongly convex on $B_{\ell_\infty}(0,1)$:
--   $$
--   \nabla^2\log\mathcal Z(\mu)\succeq L\,I\qquad\text{for all }\mu\in B_{\ell_\infty}(0,1).
--   $$
--   If the number of copies satisfies
--   $$
--   N\ \ge\ C\,4^k\alpha^{-1}\epsilon^{-2}\beta\log(m\delta^{-1})\,\min\Bigl\{\frac{m\beta}{Ln},\ \frac{m^2}{\alpha n^2\epsilon^2}\Bigr\},
--   $$
--   then there are a POVM $M$ on one copy and an estimator $\hat\mu$ of the $N$ outcomes, with values in $B_{\ell_\infty}(0,1)$, such that the following holds for every $\lambda\in B_{\ell_\infty}(0,1)$ and every Lipschitz constant $\|\cdot\|_{\mathrm{Lip}}$ for which $\sigma(\lambda)$ satisfies a transportation cost inequality with constant $\alpha$: if $M$ is applied independently to $N$ copies of $\sigma(\lambda)$, then with probability at least $1-\delta$ the Gibbs state $\sigma(\mu)$, $\mu=\hat\mu(x)$, satisfies
--   $$
--   \bigl|\operatorname{tr}[O(\sigma(\lambda)-\sigma(\mu))]\bigr|\ \le\ \epsilon\,\sqrt n\,\|O\|_{\mathrm{Lip}}\qquad\text{for all Hermitian } O .
--   $$
--
--   This is the main theorem of the paper (Theorem 1.1): under a transportation cost inequality, Gibbs states of local Hamiltonians can be learned, in a Wasserstein sense that controls all local and quasi-local observables, from a number of copies logarithmic in the number of parameters, an exponential improvement over learning each observable to relative precision.
--
--   **Formalization Note** $\|E_i\|_\infty$ is the operator norm; the Hessian is the second Fréchet derivative as a quadratic form, and $\|v\|$ is Euclidean.
--
--   Differences from the source:
--   - reading: O(4^k α^{-1} ϵ^{-2} β log(mδ^{-1}) min{mβ/(Ln), m²/(α n² ϵ²)}) samples → ∃ C > 0 universal, N ≥ C · (that expression); reason: the O(·) constant is independent of every parameter; the expression is the printed one, β¹ in the second branch of the min
--   - reading: samples of σ(λ) are sufficient to obtain → one single-copy POVM applied independently to each of N copies, then a deterministic estimator; the protocol is chosen from E, β, α, L, ε, δ, N before λ and the Lipschitz constant; reason: the stronger reading; randomized measurements are included through the outcome, and the paper's algorithm (shadows, then maximum entropy) has this form
--   - generalization: ∥·∥_Lip either of the Lipschitz constants ∥·∥_Lip,□ or ∥·∥_Lip,∇ (with the matching W_1) → every nonnegative absolutely homogeneous lip for which σ(λ) satisfies TC with constant α, quantified after λ; reason: both Lipschitz constants of the paper have these properties, so the source's statement is a special case
--   - reading: to obtain a state σ(µ) → the output is the Gibbs state σ(est x) with est x ∈ B_ℓ∞(0,1); reason: the stronger reading; σ(µ) is the paper's notation for a Gibbs state of the same family
--   - generalization: log Z is L, U strongly convex in B_ℓ∞(0,1) (UI ≥ ∇² log Z ≥ LI, f twice differentiable) → only the lower bound L‖v‖² ≤ ∇² log Z(μ)(v, v) on the ball; reason: U does not enter the conclusion or the sample bound; log Z is smooth, so twice differentiability holds; dropping a hypothesis gives a more general statement that specializes to the source's
--   - encoding: β > 0 (Def. A.1), constants α, L, ϵ > 0, δ a failure probability, n-qubit, m observables → 0 < n, 0 < m, 0 < β, 0 < α, 0 < L, 0 < ε, 0 < δ < 1; reason: these exclude only the cases where the bound is undefined (division by n, L, α, ε; log(m/δ) ≤ 0) or the claim is empty (1 − δ ≤ 0)
--   - encoding: operators on n qubits, ∥E_i∥_∞, Lipschitz observables O, D, W_1 ≤ √(D/(2α)) → complex matrices indexed by Fin n → Bool, ℓ² operator norm, Hermitian O, real parts of traces, natural-log relEnt in EReal, W1Le; reason: Lean conventions; same instances
-- source:
--   Rouzé, Stilck França, Learning quantum many-body systems from a few copies, arXiv:2107.03333v4, App. C, Theorem C.1 (Fast learning of Gibbs states), p. 26; informal form Theorem 1.1, p. 5

import Mathlib
import Definitions.Def_RouzeFranca_LearnGibbs_gibbs
import Definitions.Def_RouzeFranca_LearnGibbs_IsKLocal
import Definitions.Def_RouzeFranca_LearnGibbs_IsLipSeminorm
import Definitions.Def_RouzeFranca_LearnGibbs_SatisfiesTC
import Definitions.Def_RouzeFranca_LearnGibbs_iidProb

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RouzeFranca.LearnGibbs

/-- **Theorem C.1 (Fast learning of Gibbs states).** There is a universal constant `C > 0` with
the following property. Let `E₁, …, E_m` (`m ≥ 1`) be linearly independent Hermitian `k`-local
observables on `n ≥ 1` qubits with `‖Eᵢ‖∞ ≤ 1`, let `β, α, L, ε > 0`, `δ ∈ (0, 1)`, and assume
`μ ↦ log Z(μ)` is `L`-strongly convex on the ℓ∞ unit ball (`∇² log Z(μ) ≥ L I`). If
`N ≥ C · 4^k α⁻¹ ε⁻² β log(m/δ) · min{mβ/(Ln), m²/(α n² ε²)}`, then there are a single-copy POVM
`M` and an estimator `est` of the `N` i.i.d. outcomes, with values in the ℓ∞ unit ball, such that
for every `λ` in the ℓ∞ unit ball and every Lipschitz constant `‖·‖_Lip` for which `σ(λ)`
satisfies a transportation cost inequality with constant `α`, with probability at least `1 − δ`
the output `μ = est(x)` satisfies `|tr[O(σ(λ) − σ(μ))]| ≤ ε √n ‖O‖_Lip` for all observables `O`.

Rouzé, Stilck França, arXiv:2107.03333v4, App. C, Theorem C.1 (Fast learning of Gibbs states),
p. 26 (informal form: Theorem 1.1, p. 5): "Let σ(λ) ∈ D_{2^n} be an n-qubit Gibbs state at
inverse temperature β with respect to a set of k-local operators E = {E_i}_{i=1}^m that satisfies
a transportation cost inequality with constant α. Moreover, assume that µ ↦ log(Z(µ)) is L, U
strongly convex in B_ℓ∞(0, 1). Then O(4^k α^{-1} ϵ^{-2} β log(mδ^{-1}) min{mβ/(Ln),
m^2/(α n^2 ϵ^2)}) samples of σ(λ) are sufficient to obtain a state σ(µ) that satisfies:
|tr[O(σ(λ) − σ(µ)]| ≤ ϵ n^{1/2} ∥O∥_Lip (46) for all Lipschitz observables O with probability at
least 1 − δ."

**Formalization Note.**
1. `O(·)` is a universal constant `C`, independent of every parameter.
2. Samples: one POVM applied to each copy, i.i.d. outcomes (`iidProb`), then a deterministic
   estimator; the protocol `(K, M, est)` is chosen from the known data and `N`, before `λ` and
   the Lipschitz constant.
3. The Lipschitz constant is any `lip` with `IsLipSeminorm` (covering `‖·‖_Lip,□` and
   `‖·‖_Lip,∇`), quantified after `λ`.
4. The output state is the Gibbs state `σ(est x)` with `est x` in the ℓ∞ unit ball.
5. Strong convexity is the lower Hessian bound only (the upper constant `U` is not used by the
   conclusion); the Hessian is `fderiv ℝ (fderiv ℝ log Z) μ v v`, and `‖v‖` is Euclidean.
6. `‖Eᵢ‖` is the ℓ² operator norm; the sample bound is the printed one (`β¹` in the second branch
   of the min); `λ` is written `lam`. -/
theorem fast_learning_gibbs :
    ∃ C : ℝ, 0 < C ∧
    ∀ (n k m : ℕ) (E : Fin m → Mat n), 0 < n → 0 < m →
      (∀ i, (E i).IsHermitian) → LinearIndependent ℝ E → (∀ i, ‖E i‖ ≤ 1) →
      (∀ i, IsKLocal k (E i)) →
    ∀ (β α L ε δ : ℝ), 0 < β → 0 < α → 0 < L → 0 < ε → 0 < δ → δ < 1 →
      (∀ μ ∈ supBall m, ∀ v : EuclideanSpace ℝ (Fin m),
        L * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (logPartition E β)) μ v v) →
    ∀ N : ℕ,
      C * 4 ^ k * α⁻¹ * ε⁻¹ ^ 2 * β * Real.log (m / δ) *
          min (m * β / (L * n)) (m ^ 2 / (α * n ^ 2 * ε ^ 2)) ≤ N →
    ∃ (K : ℕ) (M : Fin K → Mat n) (est : (Fin N → Fin K) → EuclideanSpace ℝ (Fin m)),
      IsPOVM M ∧ (∀ x, est x ∈ supBall m) ∧
      ∀ lam ∈ supBall m, ∀ lip : Mat n → ℝ, IsLipSeminorm lip →
        SatisfiesTC lip α (gibbs E β lam) →
        1 - δ ≤ iidProb M (gibbs E β lam) N (fun x =>
          ∀ O : Mat n, O.IsHermitian →
            |(trace (O * (gibbs E β lam - gibbs E β (est x)))).re| ≤
              ε * Real.sqrt n * lip O) := by sorry

end RouzeFranca.LearnGibbs
