-- Prove2me | Theorems.Thm_TranspositionIID_Main_lemma_2_1
-- name    : TranspositionIID.Main.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:24:18.901325+00:00
-- url     : https://prove2.me/theorems/08e6fb27-3bbf-4903-b1d9-b2727b0a6f9f
-- title:
--   Lemma 2.1 — adaptive buffer regularity and integrability
-- statement:
--   Let $n\ge1$ and $p_1\ge\cdots\ge p_n>0$ sum to one. For the adaptive buffer $\theta$ defined by (2.2),
--   $$\operatorname{Lip}(\theta)\le\tfrac12,\qquad \frac1{2n}\le\theta(x)\le\tfrac12\quad(x\in\mathbb R),\qquad \int_{-\infty}^{0}\frac{e^x}{\theta(x)^2}\,dx\le4+32e.$$
--   The integral is finite. This controls the total cost contribution of small logarithmic separation scales.
--
--   Differences from the source:
--   - encoding: labels and charged positions 1 through n → labels and positions Fin n with charged position val + 1; reason: the order-preserving shift gives a bijection of all labels and list states
--   - encoding: r is the unique positive root of equation (2.2) → r is the infimum of its nonnegative upper level set; reason: continuity and strict increase above zero identify this finite infimum with that root for n at least one
--   - encoding: the finite improper integral over minus infinity to zero → the Lebesgue integral on Iic 0 with integrability asserted in the conclusion; reason: the endpoint has measure zero and explicit integrability prevents a default zero for a divergent integral
-- source:
--   Clayton Mizgerd, Transposition achieves OPT+O(1) in polynomial time for IID list update, STOC 2027 submission #668 (October 2026), supplied canonical submission artifact; citation basis published (not acceptance). Lemma 2.1, printed p.4 = PDF p.4; source.pdf SHA256 07dbf227a79b9907070bc1c27f25a0848cee3135ec65bcf105159f991b3b4545.

import Definitions.Def_TranspositionIID_Main_Buffer

namespace TranspositionIID.Main

/-- Lemma 2.1, printed/PDF p.4; all standing assumptions from §§1–2.1 retained. -/
theorem lemma_2_1 {n : ℕ} (hn : 1 ≤ n) (p : Fin n → ℝ)
    (hp : ActuarialValuation.isFiniteStateDistribution p)
    (hsort : Decreasing p) (hpos : ∀ i, 0 < p i) :
    LipschitzWith (1 / 2 : NNReal) (buffer p) ∧
    (∀ x : ℝ, 1 / (2 * (n : ℝ)) ≤ buffer p x ∧ buffer p x ≤ 1 / 2) ∧
    MeasureTheory.IntegrableOn (fun x : ℝ => Real.exp x / buffer p x ^ 2) (Set.Iic 0) ∧
    (∫ x : ℝ in Set.Iic 0, Real.exp x / buffer p x ^ 2) ≤ 4 + 32 * Real.exp 1 := by sorry

end TranspositionIID.Main
