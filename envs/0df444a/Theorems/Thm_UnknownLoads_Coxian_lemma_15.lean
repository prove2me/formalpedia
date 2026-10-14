-- Prove2me | Theorems.Thm_UnknownLoads_Coxian_lemma_15
-- name    : UnknownLoads.Coxian.lemma_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:36:05.588534+00:00
-- url     : https://prove2.me/theorems/8ff816d8-cc4f-45f0-a4a5-39ef8efe753b
-- title:
--   Lemma 15 — almost surely, for all large n, no pool has more than B_T tasks and the threshold stays at most B_T on [0, T]
-- statement:
--   Consider a system of the coupled construction of Section 6.1.1 and a horizon $T > 0$. There exists a positive integer $B_T$ such that, with probability one, for all sufficiently large $n$,
--   $$q_n(t, B_T + 1) = 0 \quad\text{and}\quad \ell_n(t) \le B_T \qquad \text{for all } t \in [0,T].$$
--
--   In words: on a finite horizon, the occupancy of all large systems is confined to the first $B_T$ columns and the threshold remains bounded. This is the counterpart for Coxian service of Lemma 5, and it provides property (23) of the nice sample paths.
--
--   **Formalization Note** The order is $\exists B_T$, then almost surely, then eventually in $n$; $B_T$ may depend on $T$ and on the system, not on $\omega$, while the threshold in $n$ may depend on $\omega$.
-- source:
--   Goldsztajn, Borst & van Leeuwaarden, Learning and balancing unknown loads in large-scale systems, arXiv:2012.10142v3, p. 41, Lemma 15

import Mathlib
import Definitions.Def_UnknownLoads_Coxian_Construction
open MeasureTheory Filter Topology

namespace UnknownLoads.Coxian

/-- Lemma 15 (p. 41). For every horizon `T > 0` there is a positive `B_T ∈ ℕ` such that, almost
surely, for all sufficiently large `n`, `q_n(t, B_T + 1) = 0` and `ℓ_n(t) ≤ B_T` for all
`t ∈ [0, T]`. -/
theorem lemma_15 {P : Params} {Ω : Type*} [MeasurableSpace Ω] {μP : Measure Ω}
    (sys : System P Ω μP) (T : ℝ) (hT : 0 < T) :
    ∃ BT : ℕ, 0 < BT ∧ ∀ᵐ ω ∂μP, ∀ᶠ n in atTop, ∀ t ∈ Set.Icc (0 : ℝ) T,
      sys.q n ω t (BT + 1) = 0 ∧ sys.ℓ n ω t ≤ BT := by sorry

end UnknownLoads.Coxian
