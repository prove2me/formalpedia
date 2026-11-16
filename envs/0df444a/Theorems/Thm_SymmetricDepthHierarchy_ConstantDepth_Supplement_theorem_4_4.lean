-- Prove2me | Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_Supplement_theorem_4_4
-- name    : SymmetricDepthHierarchy.ConstantDepth.Supplement.theorem_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:00:39.958311+00:00
-- url     : https://prove2.me/theorems/2281f959-53dd-4c5c-81e7-dbd62ed5bde0
-- title:
--   Theorem 4.4 — Optimal logarithmic depth for path homomorphism polynomials
-- statement:
--   Over every characteristic-zero field, P_d is the d-vertex alternating bipartite path. The degree bound holds for every n,d>=1. For n>=7 and d>=2 the displayed upper bounds hold. For each real a>=1 and real c there are a positive b and a threshold N, depending only on a,c, such that every n>=N and 2<=d<=n^a satisfies the lower bound for every symmetric circuit of orbit at most n^c computing the path polynomial. The same lower bound holds for ordinary depth. Thus both clauses hold for every source degree-bound function, uniformly in that function.
--
--   $$
--   \deg(\operatorname{hom}_{P_d,n})<d,\quad \operatorname{maxOrb}(C_n)\le n^3,\quad\operatorname{depth}(C_n)\le2\lceil\log_2d\rceil+3,\quad\operatorname{supportDepth}(C)\ge b_{c,a}\log_2d.
--   $$
--
--   This is a companion theorem; it retains all clauses of the source result and supplies its stated interface to the remaining companion results.
--
--   Differences from the source:
--   - encoding: finite circuits, patterns and positive matrix indices with polynomial and logarithmic resource bounds → the published circuit and pattern interfaces, finite ordinal witnesses, positive host indices and explicit eventual quantifiers; reason: finite relabelling preserves semantics and full automorphism orbits; index zero is outside X_n and no degree or total-size cap is added
--   - generalization: a polynomially bounded path-length family, with logarithmic upper and Omega_(c,a) lower depth bounds → pointwise degree and upper bounds, and a lower coefficient and threshold uniform in every path length and field for fixed a,c; reason: the upper proof uses no growth bound on d and supplies depth at most 2 ceil(log_2 d)+3 for n>=7; the lower proof is uniform over 2<=d<=n^a, so every source family specializes to this claim
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 12 (PDF p. 15), Theorem 4.4; source.pdf sha256 e2d54636eb14a5004f0538279b05a710bdf6487b706704a71bea70f01e7b4c42

import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Classes
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Paths

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace SymmetricDepthHierarchy.ConstantDepth.Supplement

theorem theorem_4_4 :
    (∀ (K : Type) [Field K] [CharZero K], ∀ n d : ℕ, 1 ≤ n → 1 ≤ d →
      ((pathPattern d).homPoly K n).totalDegree < d) ∧
    (∀ (K : Type) [Field K] [CharZero K], ∀ n d : ℕ, 7 ≤ n → 2 ≤ d →
      hasCircuit n ((pathPattern d).homPoly K n) (fun C =>
        C.maxOrb ≤ n^3 ∧ C.depth ≤ 2 * ⌈Real.logb 2 d⌉₊ + 3)) ∧
    (∀ a c : ℝ, 1 ≤ a → ∃ b : ℝ, 0 < b ∧ ∃ N : ℕ, ∀ (K : Type) [Field K] [CharZero K], ∀ n d : ℕ,
      1 ≤ n → N ≤ n → 2 ≤ d → (d : ℝ) ≤ Real.rpow n a →
      ∀ {V : Type} [Fintype V] (C : Circuit K n V),
        C.WellFormed → C.MatrixSymmetric →
        C.Computes ((pathPattern d).homPoly K n) →
        (C.maxOrb : ℝ) ≤ Real.rpow n c →
        b * Real.logb 2 d ≤ C.supportDepth ∧ b * Real.logb 2 d ≤ C.depth) := by sorry

end SymmetricDepthHierarchy.ConstantDepth.Supplement
