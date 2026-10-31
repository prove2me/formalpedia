-- Prove2me | Theorems.Thm_StochKolmogorov_Persist_kolmogorov_sde_face_invariance
-- name    : StochKolmogorov.Persist.kolmogorov_sde_face_invariance
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-31T03:51:04.70962+00:00
-- url     : https://prove2.me/theorems/b37a009a-38cf-4943-af74-1ee60eb73b31
-- title:
--   Invariance of the open faces of the orthant for the stochastic Kolmogorov system
-- statement:
--   If every $f_i$ and $g_i$ is locally Lipschitz on $\mathbb R^n_+$, $I\subseteq\{1,\dots,n\}$ and $x\in\mathbb R^{I,\circ}_+=\{x:x_i=0\ (i\notin I),\ x_i>0\ (i\in I)\}$, then every solution $Y$ from $x$ satisfies
--
--   $$\mathbb P\big(Y_t\in\mathbb R^{I,\circ}_+\ \text{for all } t\ge0\big)=1.$$
--
--   Role: clause 3 of Lemma 3.1 (the faces are invariant, so absent species stay absent and present ones never vanish in finite time).
-- source:
--   A. Hening, D. H. Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, https://arxiv.org/abs/1704.06984, Lemma 3.1 (3), p. 14

import Mathlib
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_StochKolmogorov_Persist_Persistence
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Persist

open EthierKurtz

theorem kolmogorov_sde_face_invariance {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (C : Coeffs n) {B : ℝ≥0 → Ω → SDEState n}
    (hB : IsStandardBrownian P B)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {I : Finset (Fin n)} {x : SDEState n} (hx : x ∈ faceOpen I) {Y : ℝ≥0 → Ω → SDEState n}
    (hY : SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x) Y) :
    ∀ᵐ ω ∂P, ∀ t, Y t ω ∈ faceOpen I := by sorry

end StochKolmogorov.Persist
