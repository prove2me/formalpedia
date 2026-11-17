-- Prove2me | Theorems.Thm_PhyloCSP_Supplement_theorem_6_2
-- name    : PhyloCSP.Supplement.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T12:28:23.582148+00:00
-- url     : https://prove2.me/theorems/74a1cf29-0e27-4594-b611-aefae2dc23b2
-- title:
--   Theorem 6.2 — thirteen NP-hard arity-4 predicates with nontrivial guarantees on completely satisfiable instances
-- statement:
--   For each of the thirteen predicates $\varphi$ of Table 1 (labels $1,\dots,4$, patterns $C_{ij}=i\mid(j\mid(k,\ell))$ and $P_2=((1,2),(3,4))$):
--
--   1. $\mathrm{CSP}(\varphi)$ is **NP-hard**: deciding complete satisfiability is NP-hard;
--   2. there is a **randomized polynomial-time algorithm** which, on every completely satisfiable instance, outputs a tree whose expected value is at least the guarantee $\alpha$ listed below; for the five algebraic guarantees, for every $\delta>0$ there is such an algorithm with expected value at least $\alpha-\delta$.
--
--   | ID | $\mathrm{Sat}(\varphi)$ | $\alpha$ |
--   |---|---|---|
--   | 1 | $\{C_{12},C_{13}\}$ | $1/4$ |
--   | 2 | $\{C_{12},C_{21}\}$ | $\frac{(x-1)(x^2-2x+2)}{5x^3-13x^2+11x-5}$, $x\in(0.1078,0.1080)$, $x^4-9x^3+17x^2-11x+1=0$ |
--   | 3 | $\{C_{13},C_{21}\}$ | $17/96$ |
--   | 6 | $\{C_{12},C_{13},C_{14},C_{21}\}$ | $1/2$ |
--   | 13 | $\{C_{12},C_{13},C_{21},C_{23}\}$ | $3/8$ |
--   | 16 | $\{C_{12},C_{13},C_{14},C_{21},C_{23}\}$ | $161/384$ |
--   | 20 | $\{C_{12},P_2\}$ | $1/4$ |
--   | 25 | $\{C_{13},C_{21},P_2\}$ | $8x^4-2x^3-4x^2+2x$, $x\in(0.2779,0.2780)$, $16x^3-3x^2-4x+1=0$ |
--   | 34 | $\{C_{12},C_{13},C_{21},C_{23},P_2\}$ | $3/8$ |
--   | 36 | $\{C_{13},C_{14},C_{21},C_{23},P_2\}$ | $\frac{3x^4-4x^3-8}{3(x^4-2x^3-8)}$, $x\in(0,1)$, $x^4+32x-24=0$ |
--   | 37 | $\{C_{12},C_{13},C_{14},C_{21},C_{23},P_2\}$ | $161/384$ |
--   | 38 | $\{C_{13},C_{14},C_{23},C_{24},P_2\}$ | $\frac{3x^4-4x^3-2}{3(x^4-2x^3-2)}$, $x\in(0,1)$, $x^4+8x-6=0$ |
--   | 39 | $\{C_{12},C_{13},C_{14},C_{23},C_{24},P_2\}$ | $\frac{3x^4-4x^3-5}{3(x^4-2x^3-4)}$, $x\in(0,1)$, $x^4+14x-9=0$ |
--
--   For each algebraic row the defining equation has exactly one root $x$ in the stated interval (this is part of the claim), and $\alpha$ is evaluated at that root; numerically the five guarantees are $\approx 0.404750$, $0.251677$, $0.341586$, $0.361455$, $0.424296$.
--
--   These are the first nontrivial approximation guarantees for completely satisfiable instances of NP-hard phylogenetic CSPs; each exceeds the trivial guarantee $\alpha_0$ of Theorem 6.1.
--
--   **Formalization Note** NP-hardness is the published `NPHardFor` for complete satisfiability of $\mathrm{CSP}(\{\varphi\})$; randomized polynomial-time approximation is `RandApproxOnSat` (a seeded polynomial-time machine that may fail on at most half of the seeds, run until it succeeds); "expected value at least $\alpha$" is stated as expected number of satisfied constraints at least $\alpha$ times the number of constraints.
--
--   Differences from the source:
--   - reading: a randomized polynomial-time approximation with the indicated guarantee, on completely satisfiable instances → RandApproxOnSat: a deterministic polynomial-time TM2 machine with a polynomial-length uniform seed that outputs a tree or fails, fails on at most half of the seeds, and whose output conditioned on success has expected number of satisfied constraints at least α times the number of constraints on every completely satisfiable instance; reason: the paper fixes no model; this is a Las Vegas algorithm with expected time at most twice a polynomial, and rejection samples exactly the uniform permutations the proof uses; expected value as in Proposition 1.7
--   - reading: "For algebraic parameters, rational approximations achieve any fixed additive loss δ > 0" → for each algebraic row: the defining equation has a unique root x in the interval of Appendix C, and for that root and every δ > 0 an algorithm with guarantee α(x) − δ exists; reason: the exact guarantees of Appendix C; uniqueness of the root is asserted on p.47 and stated as a conjunct, not assumed
--   - reading: defines an NP-hard CSP → the published NPHardFor for complete satisfiability of CSP({φ}), instances coded by encInstance; reason: NP-hard refers to the decision problem (p.2)
--   - encoding: guarantees of Table 1 (algebraic ones rounded) → the exact expressions of Appendix C; reason: Table 1 rounds; its caption points to Appendix C
--   - encoding: leaf labels 1, 2, 3, 4 → Fin 4 elements 0, 1, 2, 3; reason: Lean convention; same predicates
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Theorem 6.2, p.16 (PDF p.18); Table 1, p.15 (PDF p.17); exact parameters and guarantees, Appendix C, p.47 (PDF p.49); Proposition 1.7, p.5 (PDF p.7)

import Mathlib
import Definitions.Def_PhyloCSP_Supplement_Algorithms
import Definitions.Def_PhyloCSP_Supplement_Quartet
import Definitions.Def_IntractableCoding_Weights_NPComplete

set_option autoImplicit false

namespace PhyloCSP

namespace Supplement

open IntractableCoding.Weights

/-- Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027 submission
(manuscript sha256 3444b6c0…682dac), Theorem 6.2, p.16 (PDF p.18), with Table 1, p.15 (PDF p.17)
and the exact algebraic guarantees of Appendix C, p.47 (PDF p.49): "Each predicate in Table 1
defines an NP-hard CSP and admits, on completely satisfiable instances, a randomized
polynomial-time approximation with the indicated guarantee. For algebraic parameters, rational
approximations achieve any fixed additive loss δ > 0."

The thirteen rows (ID: `Sat(φ)`; guarantee):
`1: {C₁₂, C₁₃}; 1/4`, `2: {C₁₂, C₂₁}; algebraic`, `3: {C₁₃, C₂₁}; 17/96`,
`6: {C₁₂, C₁₃, C₁₄, C₂₁}; 1/2`, `13: {C₁₂, C₁₃, C₂₁, C₂₃}; 3/8`,
`16: {C₁₂, C₁₃, C₁₄, C₂₁, C₂₃}; 161/384`, `20: {C₁₂, P₂}; 1/4`, `25: {C₁₃, C₂₁, P₂}; algebraic`,
`34: {C₁₂, C₁₃, C₂₁, C₂₃, P₂}; 3/8`, `36: {C₁₃, C₁₄, C₂₁, C₂₃, P₂}; algebraic`,
`37: {C₁₂, C₁₃, C₁₄, C₂₁, C₂₃, P₂}; 161/384`, `38: {C₁₃, C₁₄, C₂₃, C₂₄, P₂}; algebraic`,
`39: {C₁₂, C₁₃, C₁₄, C₂₃, C₂₄, P₂}; algebraic`.
Appendix C (p.47): ID 2, "x the unique root in (0.1078, 0.1080) of x⁴ − 9x³ + 17x² − 11x + 1 = 0
… The guarantee is (x − 1)(x² − 2x + 2)/(5x³ − 13x² + 11x − 5)"; ID 25, "x the unique root in
(0.2779, 0.2780) of 16x³ − 3x² − 4x + 1 = 0 … The guarantee is 8x⁴ − 2x³ − 4x² + 2x"; IDs 36, 38,
39: x⁴ + 32x − 24 = 0, x⁴ + 8x − 6 = 0, x⁴ + 14x − 9 = 0 for x ∈ (0, 1), with guarantees
(3x⁴ − 4x³ − 8)/(3(x⁴ − 2x³ − 8)), (3x⁴ − 4x³ − 2)/(3(x⁴ − 2x³ − 2)),
(3x⁴ − 4x³ − 5)/(3(x⁴ − 2x³ − 4)); "Each equation has a unique root in (0, 1)."

For each row: `CSP(φ)` is NP-hard (the published `NPHardFor`, decision problem "completely
satisfiable", instances in the code `encInstance`); for a rational guarantee `α` there is a
randomized polynomial-time algorithm (`RandApproxOnSat`) with expected value at least `α` on every
completely satisfiable instance; for an algebraic guarantee, the defining equation has exactly one
root `x` in the stated interval and, for that root and every `δ > 0`, there is one with expected
value at least `α(x) − δ`.

**Formalization Note.** The labels `1, …, 4` are `0, …, 3` (see `C12`). The algebraic guarantees
are the exact expressions of Appendix C, not the rounded decimals of Table 1. -/
theorem theorem_6_2 :
    -- ID 1
    (NPHardFor (encInstance (L := singleLang ({C12, C13} : Predicate 4))) CompletelySatisfiable ∧
      RandApproxOnSat (singleLang ({C12, C13} : Predicate 4)) (1 / 4)) ∧
    -- ID 2
    ((∃! x : ℝ, x ∈ Set.Ioo (0.1078 : ℝ) 0.1080 ∧ x ^ 4 - 9 * x ^ 3 + 17 * x ^ 2 - 11 * x + 1 = 0) ∧
      NPHardFor (encInstance (L := singleLang ({C12, C21} : Predicate 4))) CompletelySatisfiable ∧
      ∀ x : ℝ, x ∈ Set.Ioo (0.1078 : ℝ) 0.1080 → x ^ 4 - 9 * x ^ 3 + 17 * x ^ 2 - 11 * x + 1 = 0 →
        ∀ δ : ℝ, 0 < δ → RandApproxOnSat (singleLang ({C12, C21} : Predicate 4))
          ((x - 1) * (x ^ 2 - 2 * x + 2) / (5 * x ^ 3 - 13 * x ^ 2 + 11 * x - 5) - δ)) ∧
    -- ID 3
    (NPHardFor (encInstance (L := singleLang ({C13, C21} : Predicate 4))) CompletelySatisfiable ∧
      RandApproxOnSat (singleLang ({C13, C21} : Predicate 4)) (17 / 96)) ∧
    -- ID 6
    (NPHardFor (encInstance (L := singleLang ({C12, C13, C14, C21} : Predicate 4)))
        CompletelySatisfiable ∧
      RandApproxOnSat (singleLang ({C12, C13, C14, C21} : Predicate 4)) (1 / 2)) ∧
    -- ID 13
    (NPHardFor (encInstance (L := singleLang ({C12, C13, C21, C23} : Predicate 4)))
        CompletelySatisfiable ∧
      RandApproxOnSat (singleLang ({C12, C13, C21, C23} : Predicate 4)) (3 / 8)) ∧
    -- ID 16
    (NPHardFor (encInstance (L := singleLang ({C12, C13, C14, C21, C23} : Predicate 4)))
        CompletelySatisfiable ∧
      RandApproxOnSat (singleLang ({C12, C13, C14, C21, C23} : Predicate 4)) (161 / 384)) ∧
    -- ID 20
    (NPHardFor (encInstance (L := singleLang ({C12, P2} : Predicate 4))) CompletelySatisfiable ∧
      RandApproxOnSat (singleLang ({C12, P2} : Predicate 4)) (1 / 4)) ∧
    -- ID 25
    ((∃! x : ℝ, x ∈ Set.Ioo (0.2779 : ℝ) 0.2780 ∧ 16 * x ^ 3 - 3 * x ^ 2 - 4 * x + 1 = 0) ∧
      NPHardFor (encInstance (L := singleLang ({C13, C21, P2} : Predicate 4)))
        CompletelySatisfiable ∧
      ∀ x : ℝ, x ∈ Set.Ioo (0.2779 : ℝ) 0.2780 → 16 * x ^ 3 - 3 * x ^ 2 - 4 * x + 1 = 0 →
        ∀ δ : ℝ, 0 < δ → RandApproxOnSat (singleLang ({C13, C21, P2} : Predicate 4))
          (8 * x ^ 4 - 2 * x ^ 3 - 4 * x ^ 2 + 2 * x - δ)) ∧
    -- ID 34
    (NPHardFor (encInstance (L := singleLang ({C12, C13, C21, C23, P2} : Predicate 4)))
        CompletelySatisfiable ∧
      RandApproxOnSat (singleLang ({C12, C13, C21, C23, P2} : Predicate 4)) (3 / 8)) ∧
    -- ID 36
    ((∃! x : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 ∧ x ^ 4 + 32 * x - 24 = 0) ∧
      NPHardFor (encInstance (L := singleLang ({C13, C14, C21, C23, P2} : Predicate 4)))
        CompletelySatisfiable ∧
      ∀ x : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 → x ^ 4 + 32 * x - 24 = 0 →
        ∀ δ : ℝ, 0 < δ → RandApproxOnSat (singleLang ({C13, C14, C21, C23, P2} : Predicate 4))
          ((3 * x ^ 4 - 4 * x ^ 3 - 8) / (3 * (x ^ 4 - 2 * x ^ 3 - 8)) - δ)) ∧
    -- ID 37
    (NPHardFor (encInstance (L := singleLang ({C12, C13, C14, C21, C23, P2} : Predicate 4)))
        CompletelySatisfiable ∧
      RandApproxOnSat (singleLang ({C12, C13, C14, C21, C23, P2} : Predicate 4)) (161 / 384)) ∧
    -- ID 38
    ((∃! x : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 ∧ x ^ 4 + 8 * x - 6 = 0) ∧
      NPHardFor (encInstance (L := singleLang ({C13, C14, C23, C24, P2} : Predicate 4)))
        CompletelySatisfiable ∧
      ∀ x : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 → x ^ 4 + 8 * x - 6 = 0 →
        ∀ δ : ℝ, 0 < δ → RandApproxOnSat (singleLang ({C13, C14, C23, C24, P2} : Predicate 4))
          ((3 * x ^ 4 - 4 * x ^ 3 - 2) / (3 * (x ^ 4 - 2 * x ^ 3 - 2)) - δ)) ∧
    -- ID 39
    ((∃! x : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 ∧ x ^ 4 + 14 * x - 9 = 0) ∧
      NPHardFor (encInstance (L := singleLang ({C12, C13, C14, C23, C24, P2} : Predicate 4)))
        CompletelySatisfiable ∧
      ∀ x : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 → x ^ 4 + 14 * x - 9 = 0 →
        ∀ δ : ℝ, 0 < δ → RandApproxOnSat (singleLang ({C12, C13, C14, C23, C24, P2} : Predicate 4))
          ((3 * x ^ 4 - 4 * x ^ 3 - 5) / (3 * (x ^ 4 - 2 * x ^ 3 - 4)) - δ)) := by sorry

end Supplement

end PhyloCSP
