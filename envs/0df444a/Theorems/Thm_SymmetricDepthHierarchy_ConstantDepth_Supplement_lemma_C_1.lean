-- Prove2me | Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_Supplement_lemma_C_1
-- name    : SymmetricDepthHierarchy.ConstantDepth.Supplement.lemma_C_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:59:50.455025+00:00
-- url     : https://prove2.me/theorems/f3e84895-9f9e-42ac-867d-3a14178fb808
-- title:
--   Lemma C.1 — Binomial orbit lower bound for paths
-- statement:
--   Let K have characteristic zero, Delta,k>=2, d>=1, N>=max{4(k+1),20}, and (k+1)^Delta<=min{d,N/2}. Every well-formed matrix-symmetric circuit computing hom_(P_d,N) with support depth at most Delta satisfies the bound below.
--
--   $$
--   \operatorname{maxOrb}(C)\ge\binom N{k+1}.
--   $$
--
--   This result supports Theorem 4.4; it retains all clauses of the source result and supplies its stated interface to the remaining companion results.
--
--   Differences from the source:
--   - encoding: finite circuits, patterns and positive matrix indices with polynomial and logarithmic resource bounds → the published circuit and pattern interfaces, finite ordinal witnesses, positive host indices and explicit eventual quantifiers; reason: finite relabelling preserves semantics and full automorphism orbits; index zero is outside X_n and no degree or total-size cap is added
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 41 (PDF p. 44), Lemma C.1; source.pdf sha256 e2d54636eb14a5004f0538279b05a710bdf6487b706704a71bea70f01e7b4c42

import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Classes
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Paths

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace SymmetricDepthHierarchy.ConstantDepth.Supplement

theorem lemma_C_1 (K : Type) [Field K] [CharZero K]
    (Δ k d N : ℕ) (hΔ : 2 ≤ Δ) (hk : 2 ≤ k) (hd : 1 ≤ d)
    (hN : max (4*(k+1)) 20 ≤ N) (hpow : (k+1)^Δ ≤ min d (N/2))
    {V : Type} [Fintype V] (C : Circuit K N V)
    (hw : C.WellFormed) (hs : C.MatrixSymmetric)
    (hc : C.Computes ((pathPattern d).homPoly K N)) (hdepth : C.supportDepth ≤ Δ) :
    N.choose (k+1) ≤ C.maxOrb := by sorry

end SymmetricDepthHierarchy.ConstantDepth.Supplement
