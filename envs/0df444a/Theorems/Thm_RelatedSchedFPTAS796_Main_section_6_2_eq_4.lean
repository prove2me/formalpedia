-- Prove2me | Theorems.Thm_RelatedSchedFPTAS796_Main_section_6_2_eq_4
-- name    : RelatedSchedFPTAS796.Main.section_6_2_eq_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:12:19.084419+00:00
-- url     : https://prove2.me/theorems/538700bb-bd45-40cc-9002-5a75ff923062
-- title:
--   Section 6.2, Eq. (4) — $|A\bmod\Lambda|\ge|A|/3^d$ for the lattice of a barycentric spanner
-- statement:
--   Let $A\subseteq\mathbb Z^d$ be finite and let $b_1,\dots,b_d\in A$ be a barycentric spanner of $A$ (as a subset of $\mathbb R^d$), generating $\Lambda=\mathrm{span}_{\mathbb Z}\{b_1,\dots,b_d\}$. Then every coset of $\Lambda$ meets $A$ in at most $3^d$ points, and hence
--   $$|A\bmod\Lambda|\ \ge\ \frac{|A|}{3^d}.$$
--
--   The bound is the density input of Theorem 1.3: it converts the size of $A$ into a lower bound on the number of residues modulo $\Lambda$ (p.23, "By (4) and $A\subseteq Z$").
--
--   Differences from the source:
--   - generalization: displayed inside the proof of Lemma 6.9, for $A\subseteq Z$ with $Z$ full-dimensional and $|A\bmod\Lambda'|\ge2$ for proper $\Lambda'\subsetneq Z$ → any finite $A\subseteq\mathbb Z^d$ with a barycentric spanner; reason: the displayed argument uses only the spanner property; the Lemma 6.9 setting is a special case
--   - encoding: a barycentric spanner of $A\subseteq\mathbb Z^d$ → a barycentric spanner of the image of $A$ in $\mathbb R^d$; reason: Definition 6.5 is stated over $\mathbb R^d$
-- source:
--   Lin Chen, Tingwei Hu, Jiayi Lian, Yuchen Mao, Guochuan Zhang, Faster Approximation Schemes for Scheduling on Related Machines, STOC 2027 submission #796 (October 2026), source.pdf SHA-256 5d7d0135eed9cbe942c80598e2bb07d8c56ab67aec0d6e8486a067237654f7f3, p.21, Section 6.2, Eq. (4) (in the proof of Lemma 6.9); used p.23 line 743

import Mathlib
import Definitions.Def_RelatedSchedFPTAS796_Main_Lattice

set_option autoImplicit false

namespace RelatedSchedFPTAS796.Main

/-- **Section 6.2, Eq. (4)**, p.21 (in the proof of Lemma 6.9). Let `A ⊆ ℤ^d` be finite and let
`b_1, …, b_d ∈ ℤ^d` be a barycentric spanner of `A` (viewed in `ℝ^d`), generating
`Λ = span_ℤ{b_1, …, b_d}`. Then `|A mod Λ| ≥ |A| / 3^d`. -/
theorem section_6_2_eq_4 {d : ℕ} (A : Finset (Fin d → ℤ)) (b : Fin d → Fin d → ℤ)
    (hb : IsBarycentricSpanner (toReal '' (A : Set (Fin d → ℤ))) (fun i => toReal (b i))) :
    (A.card : ℝ) / 3 ^ d ≤ Nat.card (modL (latticeGen (Set.range b)) (A : Set (Fin d → ℤ))) := by sorry

end RelatedSchedFPTAS796.Main
