-- Prove2me | Theorems.Thm_StochApproxDyn_WeakAPT_Supplement_robbinsMonro_bounded_of_lyapunov
-- name    : StochApproxDyn.WeakAPT.Supplement.robbinsMonro_bounded_of_lyapunov
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:14:37.423446+00:00
-- url     : https://prove2.me/theorems/ab709ead-c997-4538-9aea-86cb27e4698d
-- title:
--   Theorem 7.6 — a Lyapounov function with the Kushner–Yin moment conditions makes a Robbins–Monro algorithm almost surely bounded
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space with a filtration $(\mathcal F_n)$, and let
--   $$x_{n+1}-x_n=\gamma_{n+1}\big(F(x_n)+U_{n+1}\big)$$
--   be a Robbins–Monro algorithm in $\mathbb R^m$ (§4.2): $F$ is continuous, $(\gamma_n)$ is a deterministic step sequence ($\gamma_n\ge0$, $\sum\gamma_n=\infty$, $\gamma_n\to0$), $U_n$ is $\mathcal F_n$-measurable and integrable with $E(U_{n+1}\mid\mathcal F_n)=0$, and $x_0$ is $\mathcal F_0$-measurable. Suppose there are a $C^2$ function $V:\mathbb R^m\to\mathbb R_+$ with bounded second derivatives and a nonnegative function $k:\mathbb R^m\to\mathbb R_+$ such that:
--
--   1. $\langle\nabla V(x),F(x)\rangle\le-k(x)$ for all $x$;
--   2. $V(x)\to+\infty$ as $\|x\|\to\infty$;
--   3. there are constants $K,R>0$ such that $E(\|U_{n+1}\|^2+\|F(x_n)\|^2\mid\mathcal F_n)\le K\,k(x_n)$ on $\{\|x_n\|\ge R\}$ for every $n$, and
--   $$E\Big(\sum_n\gamma_{n+1}^2\big(\|U_{n+1}\|^2+\|F(x_n)\|^2\big)\mathbf 1_{\{\|x_n\|\le R\}}\Big)<\infty;$$
--   4. $E(k(x_n))<\infty$ for every $n$, and $E(V(x_0))<\infty$.
--
--   Then, with probability one,
--   $$\limsup_{n\to\infty}\|x_n\|<\infty.$$
--
--   This stability theorem (Kushner and Yin 1997, Theorem 4.3) supplies the almost sure boundedness of the iterates that the convergence results of §§4–7 assume.
--
--   **Formalization Note** Expectations of nonnegative quantities are lower Lebesgue integrals in $[0,\infty]$. For each $n$ the conditional energy in 3 is an $\mathcal F_n$-measurable function $q_n:\Omega\to[0,\infty]$ characterized by equality of its integrals with those of $\|U_{n+1}\|^2+\|F(x_n)\|^2$ over every $\mathcal F_n$-measurable set. The bound $q_n\le Kk(x_n)$ is imposed almost surely on the printed outside event. Only the compositions $k(x_n)$ are required to be measurable up to null sets for their expectations; no global measurability of $k$ or $\mathcal F_n$-measurability of $k(x_n)$ is imposed. This preserves the literal pointwise conditional bound even for such state functions. The conclusion is that $(\|x_n(\omega)\|)$ is bounded for almost every $\omega$.
--
--   Differences from the source:
--   - reading: the standing adapted-process convention of §7 → x_0 is F_0-measurable (so every x_n is F_n-measurable); reason: §7 explicitly supposes adapted paths on printed p.30 / PDF 31; the recursion propagates initial adaptedness. The conditions of §4.2 alone do not imply it.
--   - reading: a nonnegative function k → k(x_n) is measurable up to P-null sets for every n; no global measurability of k; reason: The source takes E(k(x_n)), which needs only measurability of these random variables. The literal conditional bound is retained without treating k(x_n) as F_n-measurable.
--   - reading: (iv) E(k(x_n)) < ∞ if V(x_n) < ∞ → E(k(x_n)) < ∞ for every n; reason: V is real valued, so V(x_n) < ∞ always holds.
--   - encoding: E(·|F_n) ≤ K k(x_n) on {‖x_n‖ ≥ R} → an F_n-measurable ENNReal conditional energy characterized by its integrals over every A ∈ F_n, bounded pointwise a.s. on the outside event; reason: This is the generalized nonnegative conditional expectation, with no finite-moment default and no extra measurability restriction on k.
--   - encoding: limsup ‖x_n‖ < ∞ → ∃ B, ∀ n, ‖x_n‖ ≤ B; reason: equivalent for a real sequence.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), p. 34, Theorem 7.6 (Robbins–Monro algorithm, §4.2, p. 14; scheme (7) and step-size assumptions, p. 11)

import Mathlib
import Definitions.Def_StochApproxDyn_MartingaleNoise_RobbinsMonro

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

namespace StochApproxDyn.WeakAPT.Supplement

/-- Theorem 7.6 (Benaïm 1999, p. 34; Kushner and Yin 1997, Theorem 4.3). Let
`x_{n+1} − x_n = γ_{n+1}(F(x_n) + U_{n+1})` be a Robbins–Monro algorithm (§4.2) in `ℝ^m`, with
`x_n` adapted to `ℱ_n`. Suppose there are a `C²` function `V : ℝ^m → ℝ₊` with bounded second
derivatives and a nonnegative function `k : ℝ^m → ℝ₊` such that
(i) `⟨∇V(x), F(x)⟩ ≤ −k(x)`;
(ii) `V(x) → +∞` as `‖x‖ → ∞`;
(iii) there are positive constants `K, R` with
`E(‖U_{n+1}‖² + ‖F(x_n)‖² | ℱ_n) ≤ K k(x_n)` on `{‖x_n‖ ≥ R}` and
`E(∑_n γ_{n+1}² (‖U_{n+1}‖² + ‖F(x_n)‖²) 1_{‖x_n‖ ≤ R}) < ∞`;
(iv) `E(k(x_n)) < ∞` for every `n` (`V(x_n) < ∞` always holds, `V` being real valued) and
`E(V(x_0)) < ∞`.
Then `limsup_{n → ∞} ‖x_n‖ < ∞` with probability one.

The nonnegative conditional expectation in (iii) is represented by an `ℱ_n`-measurable
function `q : Ω → ℝ≥0∞`, characterized by equality of its integrals with those of the energy
over every `ℱ_n`-measurable set. Its bound is imposed pointwise almost surely on the printed
outside event. Only the random variables `k(x_n)` must be measurable up to null sets;
no global measurability of `k` or `ℱ_n`-measurability of `k(x_n)` is added. Expectations of
nonnegative quantities are lower Lebesgue integrals in `[0, ∞]`.  -/
theorem robbinsMonro_bounded_of_lyapunov {m : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) (γ : ℕ → ℝ)
    (x U : ℕ → Ω → EuclideanSpace ℝ (Fin m))
    (hRM : StochApproxDyn.MartingaleNoise.IsRobbinsMonro P ℱ F γ x U)
    (hx0 : StronglyMeasurable[ℱ 0] (x 0))
    (V : EuclideanSpace ℝ (Fin m) → ℝ) (hV0 : ∀ y, 0 ≤ V y) (hVC2 : ContDiff ℝ 2 V)
    (hVhess : ∃ B : ℝ, ∀ y, ‖iteratedFDeriv ℝ 2 V y‖ ≤ B)
    (k : EuclideanSpace ℝ (Fin m) → ℝ) (hk0 : ∀ y, 0 ≤ k y) (hkmeas : ∀ n : ℕ, AEMeasurable (fun ω => k (x n ω)) P)
    (h_i : ∀ y, ⟪gradient V y, F y⟫_ℝ ≤ -k y)
    (h_ii : Tendsto V (cocompact _) atTop)
    (h_iii : ∃ K R : ℝ, 0 < K ∧ 0 < R ∧
      (∀ n : ℕ, ∃ q : Ω → ℝ≥0∞, Measurable[ℱ n] q ∧
        (∀ A : Set Ω, MeasurableSet[ℱ n] A →
          ∫⁻ ω in A, q ω ∂P =
            ∫⁻ ω in A, ENNReal.ofReal (‖U (n + 1) ω‖ ^ 2 + ‖F (x n ω)‖ ^ 2) ∂P) ∧
        ∀ᵐ ω ∂P, R ≤ ‖x n ω‖ → q ω ≤ ENNReal.ofReal K * ENNReal.ofReal (k (x n ω))) ∧
      ∫⁻ ω, ∑' n : ℕ, {ω | ‖x n ω‖ ≤ R}.indicator
        (fun ω => ENNReal.ofReal (γ (n + 1) ^ 2 * (‖U (n + 1) ω‖ ^ 2 + ‖F (x n ω)‖ ^ 2))) ω ∂P
        < ∞)
    (h_iv : (∀ n : ℕ, ∫⁻ ω, ENNReal.ofReal (k (x n ω)) ∂P < ∞) ∧
      ∫⁻ ω, ENNReal.ofReal (V (x 0 ω)) ∂P < ∞) :
    ∀ᵐ ω ∂P, ∃ B : ℝ, ∀ n : ℕ, ‖x n ω‖ ≤ B := by sorry

end StochApproxDyn.WeakAPT.Supplement
