-- Prove2me | Theorems.Thm_QMA2ClassicalSep_Main_theorem_6_1
-- name    : QMA2ClassicalSep.Main.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:03:17.985327+00:00
-- url     : https://prove2.me/theorems/34e75929-fc79-4464-a353-95c66c27eec8
-- title:
--   Theorem 6.1 — QMA query lower bound for the hard distributions
-- statement:
--   For every polynomial $p$ the following holds for all sufficiently large $k$. No QMA verifier with at most $p(k)$ witness qubits and $p(k)$ oracle queries to oracle (2) has both
--
--   1. completeness $2/3$ on every instance in $\operatorname{supp}\mathcal D_+$: for every YES parameter some unit witness is accepted with probability at least $2/3$; and
--   2. soundness $1/3$ on every good instance from $\mathcal D_-$: for every good NO parameter every unit witness is accepted with probability at most $1/3$.
--
--   Here a QMA verifier is a query algorithm with an $m$-qubit witness register ($m\le p(k)$), an arbitrary finite workspace in a fixed initial state, arbitrary unitaries interleaved with $q\le p(k)$ applications of $U_O$, and an accepting projector. The witness may depend on the instance. This is the lower-bound half of the separation.
--
--   Differences from the source:
--   - encoding: QMA verifier with at most p(k) witness qubits and p(k) oracle queries; polynomial p → QueryVerifier with m ≤ p(k) witness qubits, an arbitrary finite workspace, arbitrary unitaries and q ≤ p(k) applications of U_O, accepting projector; p ∈ ℕ[X]; reason: the general query model of the proof (p. 28); polynomials with natural coefficients bound every polynomial
--   - encoding: every instance in supp 𝒟₊; every good instance from 𝒟₋ → every YES parameter; every NO parameter with IsGood (block-preserving permutations, θ ∈ Θ_size, ‖Γ − Γ̄‖ ≤ 1/8); reason: 𝒟₊ is a product of uniform laws, so its support is every parameter; good parameters are by definition in supp 𝒟₋ (start of §6, p. 24)
-- source:
--   Sabee Grewal, Saachi Mutreja, Kabir Tomer, A classical oracle separation between QMA and QMA(2), STOC 2027 submission #618 (October 2026), SHA-256 79883d9d08b98b41b1bb600a6644f3f578ecb803702383a9f2a58d5bc7dacedf, p. 24, Theorem 6.1 (proof pp. 28–30)

import Definitions.Def_QMA2ClassicalSep_Main_QueryModel
import Definitions.Def_QMA2ClassicalSep_Main_HardDist

namespace QMA2ClassicalSep.Main

theorem theorem_6_1 (P : Polynomial ℕ) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ (m : ℕ) (E : Type) [Fintype E] [DecidableEq E]
      (V : QueryVerifier k (3 * k) (Fin m → Bool) E),
      m ≤ P.eval k → V.q ≤ P.eval k →
      ¬ ((∀ ω : YESParam k, ∃ w : (Fin m → Bool) → ℂ, IsUnit' w ∧
            (2 : ℝ) / 3 ≤ V.acc (yesInst ω) w) ∧
         (∀ ω : NOParam k, IsGood ω → ∀ w : (Fin m → Bool) → ℂ, IsUnit' w →
            V.acc (noInst ω) w ≤ (1 : ℝ) / 3)) := by sorry

end QMA2ClassicalSep.Main
