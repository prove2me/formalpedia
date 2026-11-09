-- Prove2me | Theorems.Thm_SuperactivatedCheating_StateConversion_gameSC_witness
-- name    : SuperactivatedCheating.StateConversion.gameSC_witness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:41:49.405133+00:00
-- url     : https://prove2.me/theorems/755c6400-c57b-4db2-801e-2a95dcea3efa
-- title:
--   Proof of Theorem 11, p. 16 — the explicit game G_SC(p, q)
-- statement:
--   A register is a finite set and $\mathcal H_A=\mathbb C^A$. A (single-round, two-party) quantum game $G=(|\psi\rangle_{ABR},\Pi_{\rm acc})$ consists of question registers $A,B$ for Alice and Bob, a referee register $R$, answer registers $a,b$, a unit question vector $\psi\in\mathcal H_A\otimes\mathcal H_B\otimes\mathcal H_R$ and an orthogonal projection $\Pi_{\rm acc}$ (Hermitian, idempotent) on $\mathcal H_a\otimes\mathcal H_b\otimes\mathcal H_R$; the answer registers are nonempty. A local strategy $S=(\mathcal E,\mathcal F)$ is a pair of quantum channels $\mathcal E:L(\mathcal H_A)\to L(\mathcal H_a)$, $\mathcal F:L(\mathcal H_B)\to L(\mathcal H_b)$, each given by a finite normalized Kraus family of any rank; there is no shared entanglement or randomness. Its winning probability is $\omega(G;S)=\operatorname{Re}\operatorname{Tr}[\Pi_{\rm acc}(\mathcal E\otimes\mathcal F\otimes\mathrm{id}_R)(|\psi\rangle\langle\psi|)]$ and the local value is $\omega(G)=\sup_S\omega(G;S)$ over all local strategies. The $n$-fold parallel repetition $G^n$ has question state $\psi^{\otimes n}$ and accepting projection $\Pi_{\rm acc}^{\otimes n}$, with Alice holding $A_1\cdots A_n$ and answering $a_1\cdots a_n$ jointly, Bob likewise, and the referee keeping $R_1\cdots R_n$.
--
--   A probability vector is a finitely indexed nonnegative real vector summing to 1. $(u\otimes v)_{(i,j)}=u_iv_j$ and $p^{\otimes n}_x=\prod_i p_{x_i}$ for strings $x$ of length $n$. "$u=v$ up to a permutation" for vectors of possibly different lengths means that their multisets of nonzero entries coincide. For probability vectors $p\in\mathbb R^k$, $q\in\mathbb R^l$, the state-conversion game $G_{SC}(p,q)$ has trivial referee register, question state $|\psi_p\rangle=\sum_i\sqrt{p_i}\,|i,i\rangle$ and accepting projection $|\phi_q\rangle\langle\phi_q|$ with $|\phi_q\rangle=\sum_j\sqrt{q_j}\,|j,j\rangle$. The witnesses are $q=(1/3,2/3)$ and $p=\frac1{201}(1,2,2,4,4,4,8,16,32,32,32,64)$, and the polynomials are $S(x)=1+x+2x^2-x^3+2x^4+x^5$ and $P(x)=(1+x)S(x)$ over $\mathbb Z$.
--
--   For the witnesses $p$, $q$, the game $G=G_{SC}(p,q)$ is a quantum game with $\omega(G)<1$ and $\omega(G^n)=1$ for every $n\ge2$.
--
--   Differences from the source:
--   - encoding: registers are finite sets and H_A = span{|a⟩ : a ∈ A} → finite types with decidable equality; vectors and operators as coordinate functions and matrices indexed by the register, joint registers as product types; reason: the standing convention of p. 9; same instances
--   - encoding: quantum channels (CPTP maps) E : L(H_A) → L(H_a), F : L(H_B) → L(H_b) → finite normalized Kraus families of any finite rank (QAlgorithms.IsKrausFamily), with E ⊗ F ⊗ id_R given by the Kraus family E_j ⊗ F_k ⊗ I_R; reason: in finite dimension the CPTP maps are exactly the maps with a finite normalized Kraus family (p. 10); every rank is allowed, so no channel is lost
--   - encoding: answer registers a, b (any finite sets) → IsQuantumGame requires a and b nonempty; reason: every register carries density operators (p. 10: D(H) and the maximally mixed state on every register); with an empty answer register there is no channel at all, so the paper's games (which are played by returning channel outputs) never have one; the question registers are nonempty because ψ is a unit vector
--   - encoding: ω(G; S) = Tr[Π_acc (E ⊗ F ⊗ id_R)(|ψ⟩⟨ψ|)] → the real part of that trace; reason: the trace of a projection times a density operator is real; same value
--   - encoding: Gⁿ = (|ψ⟩^{⊗n}, Π_acc^{⊗n}) with Alice holding A₁…A_n, Bob B₁…B_n, the referee R₁…R_n → QuantumGame.rep n on (Fin n → A) × (Fin n → B) × (Fin n → R), with ψⁿ(x,y,z) = ∏ᵢ ψ(xᵢ,yᵢ,zᵢ) and Πⁿ the product of entries; reason: this is the tensor power with the registers regrouped as on p. 12; same game
--   - reading: Definition 12 item 2: ω(G_SC) := ⟨ϕ_q|(E ⊗ F)(ψ_p)|ϕ_q⟩ → that expression is the winning probability of the strategy (E, F); the value ω(G_SC) is the §2.1 supremum localValue; reason: the printed item names the strategy's winning probability; the value is defined in §2.1
--   - encoding: 1-based indices i, j → 0-based Fin k, Fin l; reason: relabelling only
--   - encoding: the corresponding quantum game G → the conclusion explicitly asserts IsQuantumGame (G_SC(p, q)); reason: QuantumGame stores the game data and IsQuantumGame separately expresses its validity; the source already asserts that the construction is a quantum game
-- source:
--   Bhattacharyya, Mančinska, Zhao, Quantum interaction can superactivate cheating under parallel repetition, STOC 2027 submission #399 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/399.pdf, proof of Theorem 11, p. 16

import Mathlib
import Definitions.Def_SuperactivatedCheating_StateConversion_GameSC

namespace SuperactivatedCheating.StateConversion

/-- Proof of Theorem 11, p. 16: the game `G = G_SC(p, q)` with `q = (1/3, 2/3)` and
`p = (1, 2, 2, 4, 4, 4, 8, 16, 32, 32, 32, 64)/201` is a quantum game with `ω(G) < 1` and
`ω(Gⁿ) = 1` for every `n ≥ 2`. -/
theorem gameSC_witness :
    IsQuantumGame (gameSC pWit qWit) ∧ localValue (gameSC pWit qWit) < 1 ∧
      ∀ n ≥ 2, localValue ((gameSC pWit qWit).rep n) = 1 := by sorry

end SuperactivatedCheating.StateConversion
