-- Prove2me | Theorems.Thm_PrivGaussMS_eq_31
-- name    : PrivGaussMS.eq_31
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:13:13.057746+00:00
-- url     : https://prove2.me/theorems/aaf8706d-4aa9-4d55-a59b-72d0d6170a17
-- title:
--   Eq. (31) with the validity of (28) — Procedure 5 satisfies the replacement identity $\mathbb P\{\zeta\in E,\mathrm{Priv}=1\}=w\,\mathbb P\{Y_{\mathrm{priv}}\in E\}$
-- statement:
--   Let $d,m\ge1$, $0<\alpha<1$, $\eta=\alpha/(2m)$, $0<\varepsilon\le1$, integers $\lambda,a_0\ge1$, $\ell\ge1$ and $k=a_0+\lceil2\ell\rceil+1$, and assume (29):
--   $$n\ge256(m+d+1),\qquad n\ge16k\lambda,\qquad \lambda\ge16(d+2+\log n),\qquad a_0\lambda\ge16m\log(1/\eta).$$
--   Let $p=e^{-\lambda/8}/n$ and $w=(1-p)^n$. Then Procedure 5 is a probability law of the pair $(\zeta,\mathrm{Priv})$ whose proposal marginal is the proposal law, $Y_{\mathrm{priv}}$ is a probability law, and:
--
--   1. for almost every simulation $(A,U,V)$ with $|A|<k$ and $A=A_*(U,V)$, accepted or rejected, the decision probability (28) lies in $[0,1]$ simultaneously for every proposed partial batch $\zeta$;
--   2. for every measurable event $E$ of partial batches,
--   $$\mathbb P\{\zeta\in E,\ \mathrm{Priv}=1\}=w\,\mathbb E_\zeta\Bigl[\mathbf 1_{\{\zeta\in E\}}\int h_{U,V}(\zeta)\Bigl(\sum_{A\subseteq[n],|A|<k}\mathbf 1_{\{A=A_*(U,V)\}}\Bigr)d\nu(U,V)\Bigr]=w\,\mathbb P\{Y_{\mathrm{priv}}\in E\}.$$
--
--   This is the replacement identity (22) required by Lemma B.7; taking $E$ to be everything gives $\mathbb P\{\mathrm{Priv}=1\}=w$, and $1-w\le e^{-\lambda/8}$ is the extra privacy cost of the correction branch.
--
--   **Formalization Note** Procedure 5 is the explicit law `procedure5`; the decision uses an independent uniform $\tau$ and sets $\mathrm{Priv}=1$ iff $\tau$ is below (28).
--
--   Differences from the source:
--   - reading: (28) ≤ 1 (and ≥ 0) on every accepted or rejected simulation with A = A* → for almost every (A, U, V) of the simulation law with |A| < k and A = A*(U, V), simultaneously for every proposal ζ; reason: the paper sets Priv = 0 on the probability-zero exceptional frames (p.51), where D_A can be undefined
--   - reading: Procedure 5 returns the original proposal; Y_priv is the law of a partial batch → conclusions: procedure5 and Y_priv are probability measures and the ζ-marginal of procedure5 is the proposal law; reason: stated in prose on p.49 ('The proposal therefore keeps the distribution …'); it also rules out the zero measure, under which (31) would hold vacuously
--   - encoding: set Priv = 1 with probability (28) → Priv = 1 iff an independent uniform τ ∈ [0, 1] is below (28); reason: same law whenever (28) ∈ [0, 1], which the item asserts
--   - encoding: E_A an orthonormal basis of the complement of H_A in 1⊥; H_A a uniform d-frame in H_A → E_A by Gram–Schmidt of e_i − n⁻¹1 (i ∈ A); H_A = K_A Q with K_A a Helmert basis of H_A and Q uniform; reason: the paper fixes no basis and the law does not depend on it
--   - encoding: on probability-zero exceptional frames set Priv = 0; first a0 deletions on rejection → not encoded; the deletion record is truncated to its length if it is shorter than a0; reason: both concern null events and change no law
--   - encoding: the size conditions of §B.5.2 (n − k > max{m, d}, n − 1 − 2q ≥ a + d) → not assumed; reason: they follow from (29)
--   - encoding: η = α/(2m) → the parameter α ∈ (0, 1) and η := α/(2m) inside the statement; reason: same values; no instance changed
-- source:
--   Moayedi, Yassaee, Ebrahimi, Optimal Private Gaussian Multi-sampling, STOC 2027 submission (manuscript sha256 1838c582…), §B.4.4, eq. (31) and the validity bounds of (28), pp.50–51; hypotheses (29), p.50

import Mathlib
import Definitions.Def_PrivGaussMS_Correction

open MeasureTheory ProbabilityTheory

namespace PrivGaussMS

/-- **Eq. (31) with the validity of (28)**, §B.4.4, Moayedi, Yassaee, Ebrahimi, *Optimal Private
Gaussian Multi-sampling*, STOC 2027 submission (manuscript sha256 1838c582…), pp.50–51.

Under (29) and the standing parameters, Procedure 5 is well posed and satisfies the replacement
identity of Lemma B.7: the decision probability (28) lies in `[0, 1]` on every simulation with
`A = A_*(U, V)` (accepted or rejected), for every proposed partial batch; and for every measurable
event `E` of partial batches,
`P{ζ ∈ E, Priv = 1} = w E_ζ[1{ζ∈E} ∫ h_{U,V}(ζ) (Σ_{A⊆[n], |A|<k} 1{A = A_*(U,V)}) dν(U,V)]
 = w P{Y_priv ∈ E}` (31), with `w = (1 − p)^n`, `p = e^{−λ/8}/n`.

**Formalization Note.** Procedure 5 is `procedure5` (`Def_PrivGaussMS_Correction`), a law on
`(ζ, Priv)`; it is stated to be a probability law whose `ζ`-marginal is the proposal law ("the
proposal therefore keeps the distribution given by its original … rule", p.49), and `Y_priv` is
stated to be a probability law. Validity holds for almost every `(A, U, V)` of the simulation, simultaneously for every
proposal `ζ` ("These bounds hold for every proposed partial batch", p.50). Hypotheses: (29) (p.50), the standing ranges `0 < ε ≤ 1`, `0 < α < 1`, `d, m ≥ 1`
(§3), integers `λ, a0 ≥ 1`, `ℓ ≥ 1` and `k = a0 + ⌈2ℓ⌉ + 1` (§B.3.3); `η = α/(2m)`. The size
conditions of §B.5.2 (`n − k > max{m, d}`, `n − 1 − 2q ≥ a + d` for `a < k`) follow from (29). -/
theorem eq_31 (n m d k lam a0 : ℕ) (α ε ℓ : ℝ) (hm : 1 ≤ m) (hd : 1 ≤ d) (hα0 : 0 < α)
    (hα1 : α < 1) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hlam : 1 ≤ lam) (ha0 : 1 ≤ a0) (hℓ : 1 ≤ ℓ)
    (hk : k = a0 + ⌈2 * ℓ⌉₊ + 1)
    (h1 : 256 * (m + d + 1) ≤ n) (h2 : 16 * k * lam ≤ n)
    (h3 : 16 * ((d : ℝ) + 2 + Real.log n) ≤ lam)
    (h4 : 16 * (m : ℝ) * Real.log (1 / (α / (2 * m))) ≤ (a0 : ℝ) * lam) :
    IsProbabilityMeasure (procedure5 n m d lam k a0 ℓ ε (α / (2 * m))) ∧
    IsProbabilityMeasure (Ypriv n m d lam k a0 ℓ ε (α / (2 * m))) ∧
    (procedure5 n m d lam k a0 ℓ ε (α / (2 * m))).map Prod.fst =
      proposalLaw n m d (α / (2 * m)) ∧
    (∀ᵐ s ∂((setFrameLaw n d k lam).prod (laplace (2 / ε))),
      s.1.1.card < k → s.1.1 = Astar n lam k a0 ℓ s.1.2 s.2 → ∀ ζ : PartialBatch m d,
          0 ≤ decisionProb n m lam k a0 ℓ (α / (2 * m)) ζ s.1.1 s.1.2 s.2 ∧
          decisionProb n m lam k a0 ℓ (α / (2 * m)) ζ s.1.1 s.1.2 s.2 ≤ 1) ∧
    ∀ E : Set (PartialBatch m d), MeasurableSet E →
      procedure5 n m d lam k a0 ℓ ε (α / (2 * m)) (E ×ˢ ({true} : Set Bool)) =
        ENNReal.ofReal (wConst n lam) * Ypriv n m d lam k a0 ℓ ε (α / (2 * m)) E := by sorry

end PrivGaussMS
