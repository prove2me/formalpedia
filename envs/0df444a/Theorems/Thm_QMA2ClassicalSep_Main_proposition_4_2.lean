-- Prove2me | Theorems.Thm_QMA2ClassicalSep_Main_proposition_4_2
-- name    : QMA2ClassicalSep.Main.proposition_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:03:14.697787+00:00
-- url     : https://prove2.me/theorems/25eb4f82-ff56-40de-8b48-873746c63806
-- title:
--   Proposition 4.2 — the one-query QMA(2) protocol: acceptance $1-\langle\alpha,\beta|H|\alpha,\beta\rangle$
-- statement:
--   Fix $k,\ell$ and any instance $\{(\pi_p,\sigma_p)\}_{p\in[N]}$ of Problem 4.1, $N=2^k$. The protocol of the proof receives two unentangled $\ell$-qubit witnesses $|\alpha\rangle_A,|\beta\rangle_B$ and makes **one** query to oracle (2): it prepares a uniformly random $p$, the direction qubit in $|+\rangle$, queries, applies CZ between the direction qubit and the sign bit, a controlled-SWAP of the vertex and neighbor registers, and measures the direction qubit in the $\{|+\rangle,|-\rangle\}$ basis, rejecting on $|-\rangle$. Then:
--
--   1. its two gate layers are unitary and its acceptance operator is an orthogonal projector;
--   2. for all unit $\alpha,\beta$,
--   $$
--   \Pr[\text{accept}]=1-\langle\alpha,\beta|H|\alpha,\beta\rangle ;
--   $$
--   3. on a YES instance ($\lambda_{\mathrm{sep}}(H)\le3/16$) some product witness is accepted with probability at least $13/16$;
--   4. on a NO instance ($\lambda_{\mathrm{sep}}(H)\ge1/4$) every product witness is accepted with probability at most $3/4$.
--
--   Hence Problem 4.1 is solvable in QMA(2) with one query; this gives the upper bound half of the separation.
--
--   Differences from the source:
--   - reading: Problem 4.1 is solvable in QMA(2) using one query to oracle (2) → the explicit one-query circuit of the proof is unitary, accepts α⊗β with probability exactly 1 − ⟨αβ|H|αβ⟩, and has completeness ≥ 13/16 on YES and soundness ≤ 3/4 on NO; reason: this is the content established by the proof; Problem 4.1 is a promise problem about oracles, not a language
--   - encoding: Arthur samples p ∈ [N] uniformly → the p register (a k-bit string) is put in the uniform superposition by H^{⊗k} and never used again; reason: purification of the classical sample; the acceptance probability is the same average over p
-- source:
--   Sabee Grewal, Saachi Mutreja, Kabir Tomer, A classical oracle separation between QMA and QMA(2), STOC 2027 submission #618 (October 2026), SHA-256 79883d9d08b98b41b1bb600a6644f3f578ecb803702383a9f2a58d5bc7dacedf, pp. 17–18, Proposition 4.2 and its proof

import Definitions.Def_QMA2ClassicalSep_Main_QueryModel

namespace QMA2ClassicalSep.Main

theorem proposition_4_2 (k ℓ : ℕ) :
    protoU0 (k := k) (ℓ := ℓ) ∈ Matrix.unitaryGroup (QSpace k ℓ (Vtx ℓ) Unit) ℂ ∧
    protoU1 (k := k) (ℓ := ℓ) ∈ Matrix.unitaryGroup (QSpace k ℓ (Vtx ℓ) Unit) ℂ ∧
    (protoP (k := k) (ℓ := ℓ)).IsHermitian ∧
    protoP (k := k) (ℓ := ℓ) * protoP (k := k) (ℓ := ℓ) = protoP (k := k) (ℓ := ℓ) ∧
    ∀ inst : SignedInstance k ℓ,
      (∀ α β : Coord ℓ → ℂ, IsUnit' α → IsUnit' β →
        protoAcc inst α β = 1 - expect inst.Ham (prodVec α β)) ∧
      (IsYes inst → ∃ α β : Coord ℓ → ℂ, IsUnit' α ∧ IsUnit' β ∧
        (13 : ℝ) / 16 ≤ protoAcc inst α β) ∧
      (IsNo inst → ∀ α β : Coord ℓ → ℂ, IsUnit' α → IsUnit' β →
        protoAcc inst α β ≤ (3 : ℝ) / 4) := by sorry

end QMA2ClassicalSep.Main
