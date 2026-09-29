-- Prove2me | Theorems.Thm_VapnikChervonenkis_Entropy_eq12_index_append_le
-- name    : VapnikChervonenkis.Entropy.eq12_index_append_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:04:58.140985+00:00
-- url     : https://prove2.me/theorems/3184a890-a4a8-4316-9b95-e8dcb4d21adf
-- title:
--   (12) — the index of a concatenated sample is at most the product of the indices
-- statement:
--   Let $S$ be a collection of subsets of a set $X$, and let $x_1, \dots, x_k$ and $x_{k+1}, \dots, x_l$ be two samples. The index of $S$ on the concatenated sample $x_1, \dots, x_l$ is at most the product of the indices on the two parts:
--
--   $$
--   \Delta^S(x_1, \dots, x_k, x_{k+1}, \dots, x_l) \le \Delta^S(x_1, \dots, x_k)\, \Delta^S(x_{k+1}, \dots, x_l) .
--   $$
--
--   Taking binary logarithms gives the subadditivity (13) of $\log_2 \Delta^S$, from which the subadditivity of the entropy $H^S(l)$ follows.
--
--   **Formalization Note.** The two parts are `x : Fin k → X` and `y : Fin m → X`, and the concatenation is `Fin.append x y : Fin (k + m) → X`.
-- source:
--   Vapnik and Chervonenkis, On the Uniform Convergence of Relative Frequencies of Events to Their Probabilities, Theory Probab. Appl. 16 (1971), p. 272, Subsection 6, Eq. (12)

import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_index

open MeasureTheory Filter Topology

namespace VapnikChervonenkis.Entropy

/-- Display (12) of Vapnik and Chervonenkis (1971), p. 272, Subsection 6: the index of a
concatenated sample is at most the product of the indices of its two parts,
`Δ^S(x_1, ···, x_k, x_{k+1}, ···, x_l) ≤ Δ^S(x_1, ···, x_k) Δ^S(x_{k+1}, ···, x_l)`.
The two parts are `x : Fin k → X` and `y : Fin m → X` (so `l = k + m`), joined by `Fin.append`. -/
theorem eq12_index_append_le {X : Type*} (S : Set (Set X)) {k m : ℕ} (x : Fin k → X)
    (y : Fin m → X) :
    Shared.index S (Fin.append x y) ≤ Shared.index S x * Shared.index S y := by sorry

end VapnikChervonenkis.Entropy
