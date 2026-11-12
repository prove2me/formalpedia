-- Prove2me | Theorems.Thm_RelatedSchedFPTAS796_Main_lemma_6_3
-- name    : RelatedSchedFPTAS796.Main.lemma_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:12:18.961401+00:00
-- url     : https://prove2.me/theorems/2fd18509-a931-4098-9164-560872909cfc
-- title:
--   Lemma 6.3 — $|A\bmod\Lambda|=|A\bmod\widehat{\mathrm{Sym}}_{Z_\Lambda}(A)|\,|\mathrm{Sym}_{Z_\Lambda}(A)|$
-- statement:
--   Let $A\subseteq\mathbb Z^d$ and let $\Lambda\subseteq\mathbb Z^d$ be a full-rank lattice. With $\mathrm{Sym}_{Z_\Lambda}(A)$ the symmetry set of $A\bmod\Lambda$ in $Z_\Lambda=\mathbb Z^d\bmod\Lambda$ and $\widehat{\mathrm{Sym}}_{Z_\Lambda}(A)=\{g\in\mathbb Z^d: g\bmod\Lambda\in\mathrm{Sym}_{Z_\Lambda}(A)\}$ the corresponding lattice,
--   $$|A\bmod\Lambda|=\big|A\bmod\widehat{\mathrm{Sym}}_{Z_\Lambda}(A)\big|\cdot\big|\mathrm{Sym}_{Z_\Lambda}(A)\big|.$$
--
--   The identity lets the proof of Lemma 6.7 pass from residues modulo $\Lambda$ to residues modulo the coarser symmetry lattice.
--
--   Differences from the source:
--   - encoding: a full-rank (full-dimensional) lattice, $\det(\Lambda)$ → an additive subgroup of finite index, $\det$ = its index; reason: the index of a full-rank sublattice of $\mathbb Z^d$ equals the absolute determinant of any basis; same objects
-- source:
--   Lin Chen, Tingwei Hu, Jiayi Lian, Yuchen Mao, Guochuan Zhang, Faster Approximation Schemes for Scheduling on Related Machines, STOC 2027 submission #796 (October 2026), source.pdf SHA-256 5d7d0135eed9cbe942c80598e2bb07d8c56ab67aec0d6e8486a067237654f7f3, p.19, Lemma 6.3 (proof Appendix A, pp.24–25)

import Mathlib
import Definitions.Def_RelatedSchedFPTAS796_Main_Lattice

set_option autoImplicit false

namespace RelatedSchedFPTAS796.Main

/-- **Lemma 6.3**, p.19 (proof Appendix A, pp.24–25). For `A ⊆ ℤ^d` and a full-rank lattice
`Λ ⊆ ℤ^d`, `|A mod Λ| = |A mod Ŝym_{Z_Λ}(A)| · |Sym_{Z_Λ}(A)|`. -/
theorem lemma_6_3 {d : ℕ} (A : Set (Fin d → ℤ)) (Λ : AddSubgroup (Fin d → ℤ))
    (hΛ : Λ.FiniteIndex) :
    Nat.card (modL Λ A) = Nat.card (modL (symHat Λ A) A) * Nat.card (symZ Λ A) := by sorry

end RelatedSchedFPTAS796.Main
