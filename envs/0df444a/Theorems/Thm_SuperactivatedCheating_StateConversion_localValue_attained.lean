-- Prove2me | Theorems.Thm_SuperactivatedCheating_StateConversion_localValue_attained
-- name    : SuperactivatedCheating.StateConversion.localValue_attained
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:39:22.345791+00:00
-- url     : https://prove2.me/theorems/860b06b4-ef8f-496b-8ee3-f77b20bcd714
-- title:
--   §2.1, p. 11 — the local value is attained
-- statement:
--   A register is a finite set and $\mathcal H_A=\mathbb C^A$. A (single-round, two-party) quantum game $G=(|\psi\rangle_{ABR},\Pi_{\rm acc})$ consists of question registers $A,B$ for Alice and Bob, a referee register $R$, answer registers $a,b$, a unit question vector $\psi\in\mathcal H_A\otimes\mathcal H_B\otimes\mathcal H_R$ and an orthogonal projection $\Pi_{\rm acc}$ (Hermitian, idempotent) on $\mathcal H_a\otimes\mathcal H_b\otimes\mathcal H_R$; the answer registers are nonempty. A local strategy $S=(\mathcal E,\mathcal F)$ is a pair of quantum channels $\mathcal E:L(\mathcal H_A)\to L(\mathcal H_a)$, $\mathcal F:L(\mathcal H_B)\to L(\mathcal H_b)$, each given by a finite normalized Kraus family of any rank; there is no shared entanglement or randomness. Its winning probability is $\omega(G;S)=\operatorname{Re}\operatorname{Tr}[\Pi_{\rm acc}(\mathcal E\otimes\mathcal F\otimes\mathrm{id}_R)(|\psi\rangle\langle\psi|)]$ and the local value is $\omega(G)=\sup_S\omega(G;S)$ over all local strategies. The $n$-fold parallel repetition $G^n$ has question state $\psi^{\otimes n}$ and accepting projection $\Pi_{\rm acc}^{\otimes n}$, with Alice holding $A_1\cdots A_n$ and answering $a_1\cdots a_n$ jointly, Bob likewise, and the referee keeping $R_1\cdots R_n$.
--
--   For every quantum game $G$ (any finite registers) there is a local strategy $S$ with $\omega(G;S')\le\omega(G;S)$ for every local strategy $S'$, and $\omega(G;S)=\omega(G)$: the supremum is a maximum.
--
--   Differences from the source:
--   - encoding: registers are finite sets and H_A = span{|a⟩ : a ∈ A} → finite types with decidable equality; vectors and operators as coordinate functions and matrices indexed by the register, joint registers as product types; reason: the standing convention of p. 9; same instances
--   - encoding: quantum channels (CPTP maps) E : L(H_A) → L(H_a), F : L(H_B) → L(H_b) → finite normalized Kraus families of any finite rank (QAlgorithms.IsKrausFamily), with E ⊗ F ⊗ id_R given by the Kraus family E_j ⊗ F_k ⊗ I_R; reason: in finite dimension the CPTP maps are exactly the maps with a finite normalized Kraus family (p. 10); every rank is allowed, so no channel is lost
--   - encoding: answer registers a, b (any finite sets) → IsQuantumGame requires a and b nonempty; reason: every register carries density operators (p. 10: D(H) and the maximally mixed state on every register); with an empty answer register there is no channel at all, so the paper's games (which are played by returning channel outputs) never have one; the question registers are nonempty because ψ is a unit vector
--   - encoding: ω(G; S) = Tr[Π_acc (E ⊗ F ⊗ id_R)(|ψ⟩⟨ψ|)] → the real part of that trace; reason: the trace of a projection times a density operator is real; same value
-- source:
--   Bhattacharyya, Mančinska, Zhao, Quantum interaction can superactivate cheating under parallel repetition, STOC 2027 submission #399 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/399.pdf, §2.1, p. 11

import Mathlib
import Definitions.Def_SuperactivatedCheating_StateConversion_QuantumGames

namespace SuperactivatedCheating.StateConversion

/-- §2.1, p. 11: for every quantum game the local value is attained: some local strategy has
winning probability at least that of every local strategy, and it equals `ω(G)`. -/
theorem localValue_attained {A B R a b : Type*} [Fintype A] [Fintype B] [Fintype R]
    [Fintype a] [Fintype b] [DecidableEq A] [DecidableEq B] [DecidableEq R] [DecidableEq a]
    [DecidableEq b] (G : QuantumGame A B R a b) (hG : IsQuantumGame G) :
    ∃ S : LocalStrategy A B a b,
      (∀ S' : LocalStrategy A B a b, winProb G S' ≤ winProb G S) ∧
        winProb G S = localValue G := by sorry

end SuperactivatedCheating.StateConversion
