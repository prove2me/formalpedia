-- Prove2me | Theorems.Thm_TightPQRepetition_Main_lemma_5_7
-- name    : TightPQRepetition.Main.lemma_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T23:44:36.232618+00:00
-- url     : https://prove2.me/theorems/d181a7c3-3fe1-4a8b-9165-61c7bbc9db01
-- title:
--   Lemma 5.7 — inverse rotations cancel
-- statement:
--   In the setting of the hybrids, at every security parameter,
--   $$\mathrm{TD}(H_{1,3},H_{1,4})=0.$$
--   Steps 2(d) and 3(c) are conjugates of each other and are applied in succession.
--
--   Differences from the source:
--   - generalization: PPT verifier and encryption algorithms (uniform) → non-uniform families of polynomial-size Boolean circuits, with coins an explicit input and outputs of bounded, input-dependent length; reason: a uniform PPT algorithm gives such a family, so every source instance is covered; the source already takes all adversaries non-uniform (Remark 5.2)
--   - generalization: the scheme is a QFHE of Definition 2, or an FHE of Definition 1 for Remark 3.3 → any `EncScheme`: efficient classical Gen, Enc, Dec with semantic security, with no homomorphic evaluation or correctness required; reason: the verifier and the soundness proof use only these; `ClassicalFHE.toEncScheme` and `QFHE.toEncScheme` give the source's two cases
--   - encoding: each hybrid is an execution with output τ_m → each hybrid is the explicit law on its classical output: r_Query,1, r_Ver, the measured coins, messages and answers, or ⊥; measured registers are reset to 0 after recording; reason: the output determines τ_m and V(τ_1, r_Ver,1), and resetting a recorded register changes no later step
--   - encoding: rounds and coordinates numbered from 1 → numbered from 0; the source's coordinate 1 is coordinate 0; reason: same instances
--   - encoding: the circuit C^{Π_B,Π_A}_{ε,δ} of Theorem 3.9 → any rotation family with the properties of Theorem 3.9 (`IsRotationFamily`); reason: Theorem 3.9 gives one, and the lemma holds for each
--   - reading: queries q_j of unspecified length → each q_j has a length depending only on λ and j; reason: the dummy Enc(0) of Algorithm 1 is prepared before the query is known, and semantic security needs |m₀| = |m₁|, so the length must be known in advance; a verifier reaches this form by padding
--   - generalization: for simplicity Λ = ℕ and λ large enough that 2^{-λ} < ν/10k (PDF p. 25) → all λ, with no largeness condition; reason: the equality holds at every λ; at λ = 0 no attempt is made and both hybrids abort
--   - reading: B is the QPT adversary of Theorem 5.1, in an m-round protocol → B in the normal form of PDF p. 22 (no tape, trivial controller, one round per protocol round, disjoint answer registers Z_j), m ≥ 1, 1 ≤ k′ ≤ k, t′ ≤ k′, 0 < ν ≤ k; reason: these lemmas are about the objects of the proof, after its without-loss-of-generality step; Theorem 5.1 itself is stated for every QPT B; ν ≤ k follows from the source success lower bound, k′ > 1 and acceptance probability at most 1
-- source:
--   Zvika Brakerski, Andrew Huang, Yael Tauman Kalai, Nicholas Spooner, STOC 2027 submission #158 (October 2026), SHA-256 269f233ccbc44af16ba1b9aceb41299c2242cca048f65729c5fd3451cb6cd0b8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/158.pdf, Lemma 5.7, printed p. 28 / PDF p. 30

import Mathlib
import Definitions.Def_TightPQRepetition_Main_Reduction

namespace TightPQRepetition.Main

/-- Lemma 5.7 (printed p. 28, PDF p. 30). -/
theorem lemma_5_7 (x : RedCtx) (c : ℝ) (h : x.Standing c) (r0 : Fin x.m)
    (hr0 : (r0 : ℕ) = 0) :
    x.lawTD (x.hybrid .h13 r0) (x.hybrid .h14 r0) = 0 := by sorry

end TightPQRepetition.Main
