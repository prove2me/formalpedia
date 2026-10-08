-- Prove2me | Theorems.Thm_ScatCaps_Caps_baer_subplane
-- name    : ScatCaps.Caps.baer_subplane
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:05:14.875308+00:00
-- url     : https://prove2.me/theorems/ff74bc0d-23af-4407-96da-36a819537c44
-- title:
--   §1, pp. 2–3 — r = 3, t = 2 (Baer subplanes): PG(2, q²) has a scattered 𝔽_q-linear set of rank 3
-- statement:
--   Let $\mathbb F_q$ be a subfield of a finite field $K$ with $|K| = q^2$. Then there is an $\mathbb F_q$-subspace $U$ of $K^3$ of rank
--
--   $$\frac{rt}{2} = 3 \qquad (r = 3,\ t = 2)$$
--
--   whose linear set $L_U$ in $PG(2, q^2)$ is scattered (a Baer subplane, e.g. $U = \mathbb F_q^3$).
--
--   For $q = 2$ this is the existence input of Proposition 4.7 in the case $t = 2$ ($q = 4$), which Theorem 2.10 (requiring $t = 2n \ge 4$) does not cover.
-- source:
--   Bartoli, Giulietti, Marino & Polverino, Maximum scattered linear sets and complete caps in Galois spaces, arXiv:1512.07467v1, §1, pp. 2–3 (first bullet: r = 3, t = 2, Baer subplanes)

import Mathlib
import Definitions.Def_ScatCaps_LinearSets_Model

namespace ScatCaps.Caps

theorem baer_subplane (K : Type*) [Field K] [Fintype K] (Fq : Subfield K) (q : ℕ)
    (hq : Nat.card Fq = q) (hK : Fintype.card K = q ^ 2) :
    ∃ U : Set (Fin 3 → K), ScatCaps.LinearSets.IsFqSubspace Fq U ∧ ScatCaps.LinearSets.HasRank Fq U 3 ∧
      ScatCaps.LinearSets.IsScattered Fq (⊤ : Subfield K) U := by sorry

end ScatCaps.Caps
