-- Prove2me | Theorems.Thm_SuperactivatedCheating_StateConversion_Supplement_proposition_23
-- name    : SuperactivatedCheating.StateConversion.Supplement.proposition_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:23:38.680558+00:00
-- url     : https://prove2.me/theorems/980d65e8-a678-4216-b116-97495a1691f1
-- title:
--   Proposition 23 (used in the proof of Theorem 28) — product channels and product messages
-- statement:
--   Let $N_1,N_2$ be arbitrary CPTP channels between finite nonzero registers and let $M_1,M_2$ be finite nonempty message alphabets. The tensor map is CPTP and the verifier circuits satisfy
--   $$G_{\rm seq}(N_1,M_1)\times G_{\rm seq}(N_2,M_2)=G_{\rm seq}(N_1\otimes N_2,M_1\times M_2).$$
--   Equality uses the explicit canonical bijections of all message and reference wires, including removal of trivial registers. It asserts equality of preparations, middle channels on every operator and accepting projections. Joint local strategies across the two copies are allowed. This is the channel-product correspondence supporting Theorem 28.
--
--   Differences from the source:
--   - encoding: protocol equality under register regrouping and the product-message bijection → exact identity of all verifier operations under explicit canonical wire equivalences; reason: finite message alphabets M × T avoid an unnecessary choice of numbering
--   - encoding: finite-dimensional registers and CPTP operations → finite types in Type 0 with decidable equality, coordinate matrices and the published finite normalized Kraus channel predicate; reason: every finite register and every finite-dimensional CPTP map has this representation; no dimension or rank bound is imposed
--   - encoding: trace winning probabilities and local or assisted supremum values → real parts of accepting traces and real suprema over actual strategies; reason: on valid circuits the traces are real probabilities; the strategy sets are nonempty and bounded in [0,1], so no default supremum is used
--   - encoding: finite-dimensional prior shared states and local private resources → unit pure shared states and arbitrary finite retained memories; local resources are product pure states; reason: mixed resources can be purified locally without changing probabilities; every private dimension is represented by Fin e, and shared randomization cannot improve a supremum
--   - encoding: verifier sampling with private classical information or retained verification copies → the averaged initial density with a retained message or copy register, and local CPTP strategies on the received quantum registers; reason: averaging and a referee-held purification preserve all acceptance probabilities; the sampled classical description is not supplied in Hseq
-- source:
--   Bhattacharyya, Mančinska, Zhao, Quantum interaction can superactivate cheating under parallel repetition, STOC 2027 submission #399 (October 2026), Proposition 23, p. 21.

import Definitions.Def_SuperactivatedCheating_StateConversion_Supplement_Protocols

open scoped ENNReal NNReal Matrix
noncomputable section

namespace SuperactivatedCheating.StateConversion.Supplement

/-- Proposition 23, eq.(5.1), p.21: exact circuits under canonical wire bijections. -/
theorem proposition_23 {A B C D M T : Type}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype M] [Fintype T]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    [DecidableEq M] [DecidableEq T]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] [Nonempty M] [Nonempty T]
    (N : Map A B) (L : Map C D) (hN : QAlgorithms.IsChannel N) (hL : QAlgorithms.IsChannel L) :
    QAlgorithms.IsChannel (tensorMap N L) ∧ (gseqPairPorts (M := M) (T := T) N L).Respects := by sorry

end SuperactivatedCheating.StateConversion.Supplement
