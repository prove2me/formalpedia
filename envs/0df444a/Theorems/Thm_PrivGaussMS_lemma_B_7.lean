-- Prove2me | Theorems.Thm_PrivGaussMS_lemma_B_7
-- name    : PrivGaussMS.lemma_B_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:12:12.843673+00:00
-- url     : https://prove2.me/theorems/e383f2f5-f9a4-4a86-b28e-572137a6fdd8
-- title:
--   Lemma B.7 — correction using a proposal and a branch decision
-- statement:
--   Let $d,m\ge1$, $n>\max\{m,d\}$, $0<\alpha<1$, $\eta=\alpha/(2m)$, $0<\varepsilon\le1$, integers $\lambda,a_0\ge1$, $\ell\ge1$, $k=a_0+\lceil2\ell\rceil+1$. Suppose a randomized procedure independent of the input generates $\zeta$ by the proposal rule and returns $\mathrm{Priv}\in\{0,1\}$, and that for a constant $w\in[0,1]$ and every measurable event $E$,
--   $$\mathbb P\{\zeta\in E,\ \mathrm{Priv}=1\}=w\,\mathbb P\{Y_{\mathrm{priv}}\in E\}.\tag{22}$$
--   On input $x$, let $T=T(x)$. If $\mathrm{Priv}=1$, discard $\zeta$, run $\mathcal A$ with fresh randomness on the input, and independently omit positions after acceptance or use the empty partial batch after rejection. If $\mathrm{Priv}=0$, return $\Phi_T(\zeta)$ when $T\succ0$, and the empty output otherwise. Then $\mathbb P\{\mathrm{Priv}=1\}=w$, and on Gaussian input $X\sim\mathcal N(\mu,\Sigma)^{\otimes n}$, $\Sigma\succ0$, conditional on $T(X)$ the partial output has the same distribution as $\Phi_{T(X)}(\zeta)$: the joint law of $(T(X),v)$ equals the joint law of $(T(X),\Phi_{T(X)}(\zeta))$ with $\zeta$ a proposal independent of $X$.
--
--   Differences from the source:
--   - reading: 'conditional on T, the partial output has the same distribution as Φ_T(ζ)' → equality of the joint laws of (T(X), v) and (T(X), Φ_{T(X)}(ζ)), ζ an independent proposal; reason: equivalent to equality of the conditional laws given T, without conditional expectations
--   - encoding: a randomized procedure generating ζ by the proposal rule and a decision → any law ρ of (ζ, Priv) whose ζ-marginal is the proposal law, independent of X and of the fresh randomness of A_η; reason: the procedure is independent of the input
--   - reading: the lemma's parameters → n > max{m, d} and the public parameters of A (λ, a0 ≥ 1, ℓ ≥ 1, k = a0 + ⌈2ℓ⌉ + 1, 0 < ε ≤ 1); reason: standing assumptions of §B.3.1 (p.35) and §B.3.3 (p.39)
--   - generalization: A is defined for the parameters of (16) (n ≥ 16kλ, thresholds u_j defined) with n − k > max{m, d} (p.37, p.40) → not assumed; Lean's A is defined for all parameters (thresholds by Lean's total division); reason: the lemma's argument (affine equivariance of A and Lemma B.2) uses no size condition on λ, k; on the paper's parameters the Lean statement is the source's
--   - encoding: η = α/(2m) → the parameter α ∈ (0, 1) and η := α/(2m) inside the statement; reason: same values; no instance changed
-- source:
--   Moayedi, Yassaee, Ebrahimi, Optimal Private Gaussian Multi-sampling, STOC 2027 submission (manuscript sha256 1838c582…), Lemma B.7, pp.44–45, eq. (22)

import Mathlib
import Definitions.Def_PrivGaussMS_Sampler

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder

namespace PrivGaussMS

/-- **Lemma B.7** (Correction using a proposal and a branch decision), Moayedi, Yassaee, Ebrahimi,
*Optimal Private Gaussian Multi-sampling*, STOC 2027 submission (manuscript sha256 1838c582…),
pp.44–45, eq. (22).

Suppose a randomized procedure independent of the input generates `ζ` by the proposal rule and
returns `Priv ∈ {0, 1}`, and that for a constant `w ∈ [0, 1]` and every measurable `E`,
`P{ζ ∈ E, Priv = 1} = w P{Y_priv ∈ E}` (22). On input `x`, with `T = T(x)`: if `Priv = 1`, discard
`ζ` and run `A_η` on the input with fresh randomness; if `Priv = 0`, return `Φ_T(ζ)` when `T ≻ 0`
and the empty output otherwise. Then `P{Priv = 1} = w`, and on Gaussian input, conditional on `T`,
the partial output has the same distribution as `Φ_T(ζ)`.

**Formalization Note.** The procedure is any law `ρ` of `(ζ, Priv)` whose first marginal is the
proposal law. "Conditional on `T`" is stated without conditional laws: for every `µ` and `Σ ≻ 0`,
the joint law of `(T(X), v)` with `X ∼ N(µ, Σ)^{⊗n}`, `(ζ, Priv) ∼ ρ` and the fresh randomness of
`A_η` independent equals the joint law of `(T(X), Φ_{T(X)}(ζ))` with `ζ` a proposal independent of
`X`. `η = α/(2m)`. The standing assumptions are `n > max{m, d}` (p.35) and the public parameters
of `A` (§B.3.3: integers `λ, a0 ≥ 1`, `ℓ ≥ 1`, `k = a0 + ⌈2ℓ⌉ + 1`; `0 < ε ≤ 1`, `0 < α < 1`). -/
theorem lemma_B_7 (n m d lam k a0 : ℕ) (α ε ℓ : ℝ) (hm : 1 ≤ m) (hd : 1 ≤ d)
    (hmn : m < n) (hdn : d < n) (hα0 : 0 < α) (hα1 : α < 1) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hlam : 1 ≤ lam) (ha0 : 1 ≤ a0) (hℓ : 1 ≤ ℓ) (hk : k = a0 + ⌈2 * ℓ⌉₊ + 1)
    (ρ : Measure (PartialBatch m d × Bool)) (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hprop : ρ.map Prod.fst = proposalLaw n m d (α / (2 * m)))
    (h22 : ∀ E : Set (PartialBatch m d), MeasurableSet E →
      ρ (E ×ˢ ({true} : Set Bool)) =
        ENNReal.ofReal w * Ypriv n m d lam k a0 ℓ ε (α / (2 * m)) E) :
    ρ (Set.univ ×ˢ ({true} : Set Bool)) = ENNReal.ofReal w ∧
    ∀ (μ : Vec d) (Sig : Matrix (Fin d) (Fin d) ℝ), Sig.PosDef →
      ((ρ.prod (freshA n m d ε)).prod (Measure.pi fun _ : Fin n => multivariateGaussian μ Sig)).map
          (fun q => (Tstat q.2, correctedOutputFn n m d lam k a0 ℓ (α / (2 * m)) q.2 q.1)) =
        ((proposalLaw n m d (α / (2 * m))).prod
            (Measure.pi fun _ : Fin n => multivariateGaussian μ Sig)).map
          (fun q => (Tstat q.2, PhiT (Tstat q.2) q.1)) := by sorry

end PrivGaussMS
