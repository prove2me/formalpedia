-- Prove2me | Theorems.Thm_QuasiStrictNE_best_response_complexes
-- name    : QuasiStrictNE.best_response_complexes
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:10:09.019735+00:00
-- url     : https://prove2.me/theorems/75fa9dd1-7934-4db0-8f88-5b5b57d0a8cb
-- title:
--   §3, p.10 — $\mathcal C_m$, $\mathcal C_n$ are polyhedral complexes with $|\mathcal C_m|=\Delta_m$, $|\mathcal C_n|=\Delta_n$
-- statement:
--   Let $(A,B)$ be a bimatrix game with $m,n\ge 1$. Let $\mathcal C_m$ consist of all nonempty faces of the nonempty best-response regions $P_j\subseteq\Delta_m$, and $\mathcal C_n$ of all nonempty faces of the nonempty regions $Q_i\subseteq\Delta_n$. Then $\mathcal C_m$ is a polyhedral complex with
--   $$
--   |\mathcal C_m|=\Delta_m,
--   $$
--   and $\mathcal C_n$ is a polyhedral complex with $|\mathcal C_n|=\Delta_n$.
--
--   Differences from the source:
--   - reading: the intersection of any two polytopes of C is a face of each of them (Definition 3, clause 2) → the intersection is empty or a face of each (IsPolyhedralComplex); reason: faces are nonempty, so the literal clause would exclude disjoint cells; the paper only treats nonempty intersections (p.10)
--   - encoding: faces: nonempty subsets obtained by turning inequalities into equalities → nonempty exposed faces (IsExposed); reason: the two notions agree for polytopes given by inequalities; no instance changes
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), §3, p.10

import Mathlib
import Definitions.Def_QuasiStrictNE_IsPolyhedralComplex
import Definitions.Def_QuasiStrictNE_Cm
import Definitions.Def_QuasiStrictNE_Cn

namespace QuasiStrictNE

/-- **The best-response complexes** (Hansen & Nie, *On Existence and Computational Complexity of
Quasi-strict Equilibria*, arXiv:2611.06350, §3, p.10: "If Pj ∩ Pℓ ≠ ∅, their intersection is obtained
in both regions by imposing the equality (B⊤x)j = (B⊤x)ℓ, so it is a face of both. Consequently, Cm is
a polyhedral complex with |Cm| = ∆m. The same argument gives |Cn| = ∆n").

For every bimatrix game `(A, B)` with `m, n ≥ 1`, the nonempty faces `Cm` of the nonempty
best-response regions `Pj ⊆ Δm` form a polyhedral complex whose union is `Δm`, and likewise `Cn` (faces
of the regions `Qi ⊆ Δn`) is a polyhedral complex with union `Δn`.

**Formalization Note** `|C|` is `⋃₀ C`; `Δk` is `stdSimplex ℝ (Fin k)`. -/
theorem best_response_complexes {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (A B : Matrix (Fin m) (Fin n) ℝ) :
    IsPolyhedralComplex (Cm B) ∧ ⋃₀ Cm B = stdSimplex ℝ (Fin m) ∧
      IsPolyhedralComplex (Cn A) ∧ ⋃₀ Cn A = stdSimplex ℝ (Fin n) := by sorry

end QuasiStrictNE
