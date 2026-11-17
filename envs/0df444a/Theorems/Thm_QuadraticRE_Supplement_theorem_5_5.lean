-- Prove2me | Theorems.Thm_QuadraticRE_Supplement_theorem_5_5
-- name    : QuadraticRE.Supplement.theorem_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T12:56:30.932786+00:00
-- url     : https://prove2.me/theorems/1219f486-0c74-4306-984f-c3ad8bc92cbd
-- title:
--   Theorem 5.5 — one-way functions in uniform $\mathrm{NC}^1$ give uniform one-way functions of degree two and output locality three
-- statement:
--   If one-way functions exist in polynomial-time uniform $\mathrm{NC}^1$, then there exists a polynomial-time uniform family of one-way functions
--   $$g_\kappa:\mathbb F_2^{n'(\kappa)}\to\mathbb F_2^{m'(\kappa)}$$
--   of degree at most two over $\mathbb F_2$ and output locality at most three. That is, one polynomial-time machine outputs from $1^\kappa$ an explicit list of monomials, each with at most two variables, describing $g_\kappa$; each output bit of $g_\kappa$ depends on at most three input bits; and $(g_\kappa)$ is one-way against nonuniform probabilistic polynomial-time inverters.
--
--   Output locality three is optimal, since a map of output locality two can be inverted on its image by solving a 2-SAT instance; the previous best from the same assumption was locality four.
--
--   Differences from the source:
--   - generalization: one-way functions computed by polynomial-time uniform NC¹ circuits (depth O(log n) in the input length n) → circuits produced from 1^κ in polynomial time with depth ≤ c·(1 + log₂ κ) in the security parameter; reason: the circuit is produced in polynomial time, so n(κ) ≤ poly(κ) and depth O(log n(κ)) implies depth O(1 + log κ); the Lean hypothesis is weaker, so the Lean theorem specializes to the source's
--   - encoding: Boolean circuits of NC¹ → Circuit: fan-in ≤ 2, arbitrary gates, depth = longest input-to-output path; reason: p.14 fixes no basis
--   - encoding: one-way function family (nonuniform PPT adversaries, §3.1) → IsOneWay against the published Distinguisher, whose output string truncated or zero-padded is the candidate preimage; success on any preimage; reason: the paper's adversary convention; the same predicate in hypothesis and conclusion
--   - reading: a polynomial-time uniform family of degree at most two over F₂ → one polynomial-time machine mapping 1^κ to an explicit monomial description with no tape variables, every monomial of at most two variables, whose evaluation is g_κ; reason: Definition 3.2: degree is a polynomial representation of total degree ≤ 2; a uniform family is given by such a description, which also gives polynomial-time evaluation
--   - encoding: output locality at most three (each output bit depends on at most three input coordinates) → the published semantic QuadStatRE.Main.LocalLE D 3; reason: Definition 3.2, p.14; same notion
-- source:
--   Orsini, Patra, From Degree Three to Degree Two: Statistical Randomized Encodings for All Functions, STOC 2027 submission manuscript (sha256 0c94deae…), Theorem 5.5, p.33; Definition 3.2, p.14; §3.1, p.13

import Mathlib
import Definitions.Def_QuadStatRE_Main_Locality
import Definitions.Def_QuadraticRE_Supplement_OneWay

namespace QuadraticRE.Supplement

open QuadraticRE QuadStatRE.Main

/-- Theorem 5.5 of Orsini, Patra, *From Degree Three to Degree Two*, STOC 2027 submission manuscript
(sha256 0c94deae…), p.33: one-way functions with output locality three.

If one-way functions exist in polynomial-time uniform `NC¹`, then there are lengths `n′, m′` and
explicit polynomial descriptions `D_κ : F₂^{n′ κ} → F₂^{m′ κ}` (no tape variables), output by one
polynomial-time machine from `1^κ`, such that every `D_κ` has degree at most two over `F₂` and output
locality at most three (each output bit depends on at most three input bits), and the maps `D_κ` form
a one-way family.

**Formalization Note.** Degree is `Desc.DegLE 2` of the produced description and locality is the
published semantic `QuadStatRE.Main.LocalLE` (Definition 3.2, p.14). One-wayness in the hypothesis and
in the conclusion is the same predicate `IsOneWay` against the base mission's nonuniform PPT
adversaries. A uniform family is evaluated from its polynomial-size description in polynomial time. -/
theorem theorem_5_5 (h : OWFInUniformNC1) :
    ∃ (n' m' : ℕ → ℕ) (D : ∀ κ, Desc (n' κ) 0 (m' κ)),
      PolyTimeFn encNat (fun κ => encDesc (D κ)) ∧
      (∀ κ, (D κ).DegLE 2 ∧ LocalLE (D κ) 3) ∧
      IsOneWay n' m' (fun κ x => (D κ).eval x Fin.elim0) := by sorry

end QuadraticRE.Supplement
