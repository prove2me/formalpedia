-- Prove2me | Theorems.Thm_WildeQIT_Activation_theorem_24_8_1
-- name    : WildeQIT.Activation.theorem_24_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T19:14:20.131853+00:00
-- url     : https://prove2.me/theorems/711963a9-ff84-400f-8a41-f1c48f7a8d0a
-- title:
--   Theorem 24.8.1 — a 50% erasure channel turns half the private information into coherent information
-- statement:
--   **Theorem 24.8.1.** Let $\{p_X(x),\rho^x_{A_2}\}$ be an ensemble of inputs for the channel $\mathcal N_2$, and let $\mathcal N_1$ be a 50% erasure channel. Then there exists a pure state $\phi_{RA_1A_2}$ such that the coherent information $H(B_1B_2)-H(E_1E_2)$ of the joint channel $\mathcal N_1\otimes\mathcal N_2$ equals half the private information $I(X;B_2)-I(X;E_2)$ of the second channel:
--
--   $$
--   H(B_1B_2)_\omega-H(E_1E_2)_\omega=\tfrac12\left[I(X;B_2)_\rho-I(X;E_2)_\rho\right],
--   $$
--
--   where
--
--   $$
--   \omega_{RB_1B_2E_1E_2}\equiv\left(U^{\mathcal N_1}_{A_1\to B_1E_1}\otimes U^{\mathcal N_2}_{A_2\to B_2E_2}\right)(\phi_{RA_1A_2}),\qquad
--   \rho_{XB_2E_2}\equiv\sum_x p_X(x)\,|x\rangle\langle x|_X\otimes U^{\mathcal N_2}_{A_2\to B_2E_2}(\rho^x_{A_2}),
--   $$
--
--   and $U^{\mathcal N_1}$, $U^{\mathcal N_2}$ are isometric extensions of $\mathcal N_1$, $\mathcal N_2$. This implies
--
--   $$
--   Q(\mathcal N_1\otimes\mathcal N_2)\ge P(\mathcal N_2)/2 ,
--   $$
--
--   with $Q$ the channel coherent information (24.9) and $P$ the private information (13.179).
--
--   The statement has two parts:
--
--   1. for every ensemble and every 50% erasure channel $\mathcal N_1$ whose input dimension is at least $|\mathcal X|\cdot\dim\mathcal H_{A_2}$, a pure state $\phi_{RA_1A_2}$ with the displayed identity exists;
--   2. there is an input dimension $n$, depending only on $\mathcal N_2$, such that $Q(\mathcal N_1\otimes\mathcal N_2)\ge P(\mathcal N_2)/2$ for every 50% erasure channel $\mathcal N_1$ with input dimension at least $n$.
--
--   Combined with an entanglement-binding channel $\mathcal N_2$, which has zero quantum capacity but positive private information, this gives superactivation: two channels of zero quantum capacity whose tensor product has positive quantum capacity.
--
--   **Formalization Note** Channels are Kraus families (`WildeQIT.QChannel`), with the Kraus-built isometric extensions; entropies are the published `QAlgorithms.vnEntropy`, in bits; the reference $R$ has any finite dimension. Finite dimensions throughout, the book's setting.
--
--   Differences from the source:
--   - reading: "a 50% erasure channel" with no input dimension given → in part 1 an input dimension at least |X|·dim A2, in part 2 an input dimension at least some n depending only on N2; reason: the proof identifies A1 ≡ A′1A′′1 with A′1 ≅ H_X and A′′1 ≅ H_A2 (24.168), and for a one-dimensional input N1 only outputs a flag, so (24.166) would claim Q(N2) ≥ P(N2)/2, false for the entanglement-binding channel of p. 686; since P(N2) is a maximum over ensembles of every size, (24.166) needs N1 large enough for a maximizing ensemble
--   - encoding: quantum channels N1, N2 → WildeQIT.QChannel Kraus families; reason: every finite-dimensional channel has a Kraus form (Theorem 4.4.1); same instances
--   - encoding: arbitrary isometric extensions U^N1, U^N2 → the Kraus-built extensions sum_i K_i ⊗ |i⟩_E; reason: two isometric extensions differ by an isometry on the environment, which leaves H(B1B2), H(E1E2), I(X;B2) and I(X;E2) unchanged
--   - encoding: the 50% erasure channel ρ ↦ ½ρ + ½|e⟩⟨e| on density operators → the linear map ρ ↦ ½VρV† + ½Tr(ρ)|e⟩⟨e| for an isometry V and a unit vector e orthogonal to its range, into any output space containing both; reason: the unique linear extension of the book's map, and (24.5) fixes the output space only as containing the input and |e⟩; same channels
--   - encoding: Q and P defined as maxima → real suprema over pure inputs with reference Fin k and over ensembles with alphabet Fin k, k arbitrary; reason: the values are bounded above and the maxima are attained, so the numbers agree
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 24.8.1, eqs. (24.163)–(24.166), p. 684

import Definitions.Def_WildeQIT_Activation_IsHalfErasure
import Definitions.Def_WildeQIT_Activation_omegaState
import Definitions.Def_WildeQIT_Activation_privateInfoChannel
import Definitions.Def_WildeQIT_Activation_coherentInfoChannel
import Definitions.Def_WildeQIT_Degradable_tensorChannel

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 24.8.1, p. 684, eqs. (24.163)–(24.166).
-/

open Matrix

namespace WildeQIT.Activation

open Classical in
/-- **Theorem 24.8.1** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 684). Let `{p_X(x), ρˣ_{A2}}` be an ensemble of inputs for the
channel `N2`, and let `N1` be a 50% erasure channel. Then there exists a pure state `ϕ_{RA1A2}`
such that `H(B1B2)_ω − H(E1E2)_ω = ½ [I(X; B2)_ρ − I(X; E2)_ρ]` (24.163), where
`ω ≡ (U^{N1} ⊗ U^{N2})(ϕ)` (24.164) and `ρ_{XB2E2} ≡ ∑ₓ p_X(x)|x⟩⟨x|_X ⊗ U^{N2}(ρˣ_{A2})`
(24.165). This implies `Q(N1 ⊗ N2) ≥ P(N2)/2` (24.166).

**Formalization Note.** Two conjuncts.
1. (24.163): for every ensemble `E` with alphabet `Fin E.k` and every 50% erasure channel `N1`
   whose input dimension is at least `|X| · dim A2` (the book's proof identifies
   `A1 ≡ A′1A′′1` with `A′1 ≅ H_X` and `A′′1 ≅ H_{A2}`, (24.168)), a pure input `ϕ_{RA1A2}`
   (`PureInput`, reference `Fin k`) exists with the stated identity. `H(B1B2)_ω` is the entropy
   of `Tr_{E1E2} Tr_R ω` and `H(E1E2)_ω` that of `Tr_{B1B2} Tr_R ω`, with `ω = omegaState`
   built from the canonical isometric extensions; any other isometric extensions give the same
   entropies. The right-hand side is `privateInfoEnsemble N2 E / 2`.
2. (24.166): `Q` is the channel coherent information (24.9) and `P` the private information
   (13.179). Since `P(N2)` is a maximum over ensembles of every size, the 50% erasure channel
   `N1` must be large enough for a maximizing ensemble: there is an input dimension `n`,
   depending only on `N2`, such that `Q(N1 ⊗ N2) ≥ P(N2)/2` for every 50% erasure channel `N1`
   with input dimension at least `n`. -/
theorem theorem_24_8_1 {a2 b2 : Type} [Fintype a2] [DecidableEq a2] [Fintype b2] [DecidableEq b2]
    (N2 : QChannel a2 b2) :
    (∀ (E : WildeQIT.Degradable.CQInput a2) {a1 b1 : Type} [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
        (N1 : QChannel a1 b1), IsHalfErasure N1 → E.k * Fintype.card a2 ≤ Fintype.card a1 →
        ∃ ϕ : PureInput (a1 × a2),
          QAlgorithms.vnEntropy (partialTraceRight (partialTraceLeft (omegaState N1 N2 ϕ.vec))) -
              QAlgorithms.vnEntropy (partialTraceLeft (partialTraceLeft (omegaState N1 N2 ϕ.vec))) =
            privateInfoEnsemble N2 E / 2) ∧
    (∃ n : ℕ, ∀ {a1 b1 : Type} [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
        (N1 : QChannel a1 b1), IsHalfErasure N1 → n ≤ Fintype.card a1 →
        privateInfoChannel N2 / 2 ≤ coherentInfoChannel (WildeQIT.Degradable.tensorChannel N1 N2)) := by sorry

end WildeQIT.Activation
