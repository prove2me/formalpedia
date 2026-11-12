-- Prove2me | Theorems.Thm_QuantumGroupCodes836_Addressability_lifted_code_parameters
-- name    : QuantumGroupCodes836.Addressability.lifted_code_parameters
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T17:12:06.000696+00:00
-- url     : https://prove2.me/theorems/c89d8172-828c-46e4-a583-c62159178218
-- title:
--   Corollary 4.5 — lifted code, dual freeness and parameters
-- statement:
--   Under the hypotheses of Theorem 4.4, let $C=C_L(P,D)$ have actual dimension $k$ and length $n$. There is an unramified lift to the quadratic constant field, with $\widetilde C=C_L(\operatorname{Con}P,\operatorname{Con}D)$, abelian group $G$ and preserved multiplication property. The code and dual are free modules of ranks $k$ and $n-k$, for the same coordinate action, and
--
--   $$\widetilde n=n|G|,\quad\widetilde k=k|G|,\quad\widetilde k^\perp=(n-k)|G|,$$
--   $$\widetilde d\ge(n-\deg D)|G|,\qquad\widetilde d^\perp\ge(\deg D-2g+2)|G|.$$
--
--   The order bound is $|G|\ge(\sqrt q-1)^{2g}$, where $q$ is the base alphabet size. These are all six source clauses; the lifted code is constructed from actual evaluation and conorm maps.
--
--   Differences from the source:
--   - encoding: function fields, places, divisors and differentials → finite extensions with full constants, valuation-ring places, finitely supported divisors and Kähler differentials; reason: no separating chart, lifting existence or parameter bound is assumed; regular differential dimension computes genus
--   - encoding: finite coordinate sets and Hamming minima → zero-based finite types, actual submodules and extended-natural minima; reason: relabeling changes no code; the zero code has infinite distance
--   - generalization: an unramified extension F̃/F with G abelian → also: constants of size q², separable, Galois over the constant extension F′=F·F_{q²}, G = Aut(F̃/F′) acting on the coordinates as on the places; reason: these are the properties of the extension of Theorem 4.4 that defines G := Gal(F̃_H/F′); the Lean conclusion implies the source one
-- source:
--   Virgile Guemard, Jean Gasnier, STOC 2027 submission #836 (October 2026), Corollary 4.5, p.17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/836.pdf

import Definitions.Def_QuantumGroupCodes836_Addressability_Lifting

set_option autoImplicit false

namespace QuantumGroupCodes836.Addressability

theorem lifted_code_parameters {k : Type} [Field k] [Fintype k] (F : FunctionFieldData k)
    (P : EvaluationData F) (D : Divisors F) (m : ℕ) (η : KaehlerDifferential k F.carrier)
    (h : AGAssumptions P D m η) :
    ∃ L : LiftData F, LiftCodeProperties P D m L ∧
      (Real.sqrt (Fintype.card k) - 1) ^ (2 * genus F) ≤ (Nat.card L.group : ℝ) := by sorry

end QuantumGroupCodes836.Addressability
