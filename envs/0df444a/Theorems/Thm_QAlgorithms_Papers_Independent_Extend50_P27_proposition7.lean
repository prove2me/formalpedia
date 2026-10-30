-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P27_proposition7
-- name    : QAlgorithms.Papers.Independent.Extend50.P27.proposition7
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:38:55.359403+00:00
-- url     : https://prove2.me/theorems/c9ba21e7-a3e0-4cf4-8569-a0b4fe12463c
-- title:
--   Proposition 7: character-table diagonalization
-- statement:
--   Let $N\ge1$. The full teleportation matrix $M_N$ is indexed by all $N$-box Young diagrams, with removable-corner counts on the diagonal and one on distinct single-box-move pairs. For $d\ge1$, $M_N^{(d)}$ is its principal restriction to shapes of height at most $d$, retaining the same diagonal counts.
--
--   For a Young diagram $\mu$, let $S^\mu$ be its complex Specht module, constructed as a Young left ideal, and $d_\mu=\dim S^\mu$. Restriction from $S_N$ to $S_{N-1}$ uses the subgroup fixing the last letter; induction uses this subgroup. Occurrence and multiplicity refer to actual modules, equivalently to dimensions of their intertwiner spaces.
--
--   For each conjugacy class $C$ of $S_N$, let $k(C)$ be the number of fixed points and let $T(C)=(\chi_\mu(C))_\mu$. With the literal unweighted character table $T=(T(C))_C$,
--
--   $$
--   M_NT(C)=k(C)T(C),\qquad T^{-1}M_NT=\operatorname{diag}(k(C))_C.
--   $$
--
--   The table is invertible; no unitarity is asserted. This gives a complete character-based diagonalization.
-- source:
--   Optimal Port-based Teleportation, arXiv:1707.08456v1, PDF p. 9, Proposition 7: character-table diagonalization

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P27

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

open QAlgorithms.Schur

namespace QAlgorithms.Papers.Independent.Extend50.P27

open QAlgorithms.Papers.Independent.Renew46.P26 (deleteLast)

open QAlgorithms.Papers.Independent.Gap20.P01 (spechtMatrix)

open QAlgorithms.Papers.Independent.Claimed50.P28 (traceInput)

attribute [local instance] Classical.propDecidable

/-- Proposition 7, unweighted character eigenvectors and invertible diagonalization
(PDF pp.9–10). The false preceding unitarity claim is not included. -/
theorem proposition7 {N : ℕ} (hN : 0 < N) :
    (∀ (pi : Equiv.Perm (Fin N)) (nu : Partition N N),
      (∑ mu : Partition N N, (fullMatrix N nu mu : ℂ) * spechtCharacter mu pi) =
        (fixedCount pi : ℂ) * spechtCharacter nu pi) ∧
    (∃ S : Matrix (ConjClasses (Equiv.Perm (Fin N))) (Partition N N) ℂ,
      characterTable N * S = 1 ∧ S * characterTable N = 1 ∧
      (fullMatrix N).map (fun x => (x : ℂ)) * characterTable N =
        characterTable N * Matrix.diagonal
          (fun C : ConjClasses (Equiv.Perm (Fin N)) =>
            (fixedCount (Quotient.out C) : ℂ))) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P27

end
