-- Prove2me | Theorems.Thm_ScatCaps_LinearSets_baer_subplane
-- name    : ScatCaps.LinearSets.baer_subplane
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:09:11.757276+00:00
-- url     : https://prove2.me/theorems/dc04ed57-ebe6-49dd-991a-a7c890122e6f
-- title:
--   §1, pp. 2–3 — r = 3, t = 2: a scattered 𝔽_q-linear set of rank 3 in PG(2, q²) (Baer subplanes)
-- statement:
--   Let $\mathbb F_q\subseteq\mathbb F_{q^2}$ be finite fields. There is an $\mathbb F_q$-subspace $U$ of $V=\mathbb F_{q^2}^{\,3}$ with $\dim_{\mathbb F_q}U=3$ whose linear set
--
--   $$
--   L_U=\{\langle u\rangle_{\mathbb F_{q^2}}: u\in U\setminus\{0\}\}\subseteq\mathrm{PG}(2,q^2)
--   $$
--
--   is scattered; it attains the upper bound $rt/2=3$. The paper lists this case ("Baer subplanes") among the odd-$r$ cases where $rt/2$ is attained; it is the $t=2$ plane case needed for Theorem 1.2.
--
--   **Formalization Note** Rank $3$ is $|U|=q^3$, and points are $\mathbb F_{q^2}$-spans in `Fin 3 → K`.
-- source:
--   Bartoli, Giulietti, Marino & Polverino, Maximum scattered linear sets and complete caps in Galois spaces, arXiv:1512.07467v1, pp. 2–3, §1, first bullet (r = 3, t = 2, Baer subplanes)

import Mathlib
import Definitions.Def_ScatCaps_LinearSets_Model

namespace ScatCaps.LinearSets

theorem baer_subplane (K : Type*) [Field K] [Fintype K]
    (Fq : Subfield K) (q : ℕ)
    (hq : Nat.card Fq = q) (hK : Fintype.card K = q ^ 2) :
    ∃ U : Set (Fin 3 → K), IsFqSubspace Fq U ∧
      HasRank Fq U 3 ∧ IsScattered Fq (⊤ : Subfield K) U := by sorry

end ScatCaps.LinearSets
