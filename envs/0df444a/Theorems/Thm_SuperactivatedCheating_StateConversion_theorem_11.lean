-- Prove2me | Theorems.Thm_SuperactivatedCheating_StateConversion_theorem_11
-- name    : SuperactivatedCheating.StateConversion.theorem_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:39:17.560968+00:00
-- url     : https://prove2.me/theorems/86e4e3a4-8426-4798-a890-afba912660be
-- title:
--   Theorem 11 — a quantum game with local value below one whose every parallel repetition is won perfectly
-- statement:
--   A register is a finite set and $\mathcal H_A=\mathbb C^A$. A (single-round, two-party) quantum game $G=(|\psi\rangle_{ABR},\Pi_{\rm acc})$ consists of question registers $A,B$ for Alice and Bob, a referee register $R$, answer registers $a,b$, a unit question vector $\psi\in\mathcal H_A\otimes\mathcal H_B\otimes\mathcal H_R$ and an orthogonal projection $\Pi_{\rm acc}$ (Hermitian, idempotent) on $\mathcal H_a\otimes\mathcal H_b\otimes\mathcal H_R$; the answer registers are nonempty. A local strategy $S=(\mathcal E,\mathcal F)$ is a pair of quantum channels $\mathcal E:L(\mathcal H_A)\to L(\mathcal H_a)$, $\mathcal F:L(\mathcal H_B)\to L(\mathcal H_b)$, each given by a finite normalized Kraus family of any rank; there is no shared entanglement or randomness. Its winning probability is $\omega(G;S)=\operatorname{Re}\operatorname{Tr}[\Pi_{\rm acc}(\mathcal E\otimes\mathcal F\otimes\mathrm{id}_R)(|\psi\rangle\langle\psi|)]$ and the local value is $\omega(G)=\sup_S\omega(G;S)$ over all local strategies. The $n$-fold parallel repetition $G^n$ has question state $\psi^{\otimes n}$ and accepting projection $\Pi_{\rm acc}^{\otimes n}$, with Alice holding $A_1\cdots A_n$ and answering $a_1\cdots a_n$ jointly, Bob likewise, and the referee keeping $R_1\cdots R_n$.
--
--   There exist finite registers $A,B,R,a,b$ and a quantum game $G$ on them with $\omega(G)<1$ and $\omega(G^n)=1$ for every $n\ge2$.
--
--   Differences from the source:
--   - encoding: registers are finite sets and H_A = span{|a⟩ : a ∈ A} → finite types with decidable equality; vectors and operators as coordinate functions and matrices indexed by the register, joint registers as product types; reason: the standing convention of p. 9; same instances
--   - encoding: quantum channels (CPTP maps) E : L(H_A) → L(H_a), F : L(H_B) → L(H_b) → finite normalized Kraus families of any finite rank (QAlgorithms.IsKrausFamily), with E ⊗ F ⊗ id_R given by the Kraus family E_j ⊗ F_k ⊗ I_R; reason: in finite dimension the CPTP maps are exactly the maps with a finite normalized Kraus family (p. 10); every rank is allowed, so no channel is lost
--   - encoding: answer registers a, b (any finite sets) → IsQuantumGame requires a and b nonempty; reason: every register carries density operators (p. 10: D(H) and the maximally mixed state on every register); with an empty answer register there is no channel at all, so the paper's games (which are played by returning channel outputs) never have one; the question registers are nonempty because ψ is a unit vector
--   - encoding: ω(G; S) = Tr[Π_acc (E ⊗ F ⊗ id_R)(|ψ⟩⟨ψ|)] → the real part of that trace; reason: the trace of a projection times a density operator is real; same value
--   - encoding: Gⁿ = (|ψ⟩^{⊗n}, Π_acc^{⊗n}) with Alice holding A₁…A_n, Bob B₁…B_n, the referee R₁…R_n → QuantumGame.rep n on (Fin n → A) × (Fin n → B) × (Fin n → R), with ψⁿ(x,y,z) = ∏ᵢ ψ(xᵢ,yᵢ,zᵢ) and Πⁿ the product of entries; reason: this is the tensor power with the registers regrouped as on p. 12; same game
--   - encoding: there exists a quantum game (registers any finite sets) → an existential over types in Type 0 with Fintype and DecidableEq instances; reason: every finite set is equivalent to a finite type in Type 0; same games
-- source:
--   Bhattacharyya, Mančinska, Zhao, Quantum interaction can superactivate cheating under parallel repetition, STOC 2027 submission #399 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/399.pdf, Theorem 11, p. 15 (proof pp. 15–16)

import Mathlib
import Definitions.Def_SuperactivatedCheating_StateConversion_QuantumGames

namespace SuperactivatedCheating.StateConversion

/-- Theorem 11, p. 15: there exists a quantum game `G` such that `ω(G) < 1` but `ω(Gⁿ) = 1` for
all `n ≥ 2`, where `ω` is the local (unentangled) value. -/
theorem theorem_11 :
    ∃ (A B R a b : Type) (_ : Fintype A) (_ : Fintype B) (_ : Fintype R) (_ : Fintype a)
      (_ : Fintype b) (_ : DecidableEq A) (_ : DecidableEq B) (_ : DecidableEq R)
      (_ : DecidableEq a) (_ : DecidableEq b) (G : QuantumGame A B R a b),
      IsQuantumGame G ∧ localValue G < 1 ∧ ∀ n ≥ 2, localValue (G.rep n) = 1 := by sorry

end SuperactivatedCheating.StateConversion
