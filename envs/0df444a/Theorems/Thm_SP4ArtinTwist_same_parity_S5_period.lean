-- Prove2me | Theorems.Thm_SP4ArtinTwist_same_parity_S5_period
-- name    : SP4ArtinTwist.same_parity_S5_period
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-08T02:03:21.936221+00:00
-- url     : https://prove2.me/theorems/e22ceef3-63d4-49ad-b9df-8f01d932c290
-- title:
--   Artin full-twist conjugation and period 30 for equal-parity pairs in $S_5$
-- statement:
--   Let $S_5$ be the permutation group on five letters, with multiplication given by composition. On ordered pairs define the invertible Artin action and its full twist by
--
--   $$
--   A(a,b)=(aba^{-1},a),\qquad T=A^2.
--   $$
--
--   Let $a,b\in S_5$ have the same permutation sign, and put $g=ab$. Then
--
--   $$
--   g^{30}=1.
--   $$
--
--   Every nonnegative iterate of the actual full-twist action is simultaneous conjugation:
--
--   $$
--   T^m(a,b)=\bigl(g^mag^{-m},\;g^mbg^{-m}\bigr)
--   \qquad(m\in\mathbb N).
--   $$
--
--   Moreover, the orbit has period dividing thirty for all integer times:
--
--   $$
--   T^{n+30}(a,b)=T^n(a,b)
--   \qquad(n\in\mathbb Z).
--   $$
--
--   Negative iterates use the inverse of the explicitly defined Artin permutation. Thirty is a sufficient period, not a claim that each pair has least period thirty.
--
--   This theorem isolates the finite-group input to a proposed full-twist cover-count argument. It concerns only the displayed action on permutation pairs. Connecting these pairs to knot-group representations, proving a gluing bijection, and passing to connected unbased covers are separate tasks and are not conclusions of this theorem.
-- source:
--   Local research note, Cycle 9, Finite-cover counts in a fixed full-twist family, Proof: the displayed Artin generator, its square, and the paragraph deriving (ab)^30=1 for same-parity S5 images. Independent critical audit, Sections 1 and 3. Only these local group-algebra assertions are formalized; representation gluing and cover-count periodicity are excluded. Source note cycle9_twist_cover_periodicity.md, SHA-256 c4b995489cb5910bd0a9371cf5e6e272c56672116851a613c46eab69a5d82408.

import Definitions.Def_SP4ArtinTwist
import Mathlib.GroupTheory.Perm.Sign

set_option autoImplicit false

open SP4ArtinTwist

theorem SP4ArtinTwist.same_parity_S5_period (a b : Equiv.Perm (Fin 5))
    (hparity : Equiv.Perm.sign a = Equiv.Perm.sign b) :
    (a * b) ^ (30 : ℕ) = 1 ∧
    (∀ m : ℕ, (fullTwist (Equiv.Perm (Fin 5)) ^ m) (a, b) =
      ((a * b)^m * a * ((a * b)^m)⁻¹, (a * b)^m * b * ((a * b)^m)⁻¹)) ∧
    (∀ n : ℤ, (fullTwist (Equiv.Perm (Fin 5)) ^ (n + 30)) (a, b) =
      (fullTwist (Equiv.Perm (Fin 5)) ^ n) (a, b)) := by sorry
