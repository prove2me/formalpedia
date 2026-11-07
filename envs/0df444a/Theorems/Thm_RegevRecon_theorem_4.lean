-- Prove2me | Theorems.Thm_RegevRecon_theorem_4
-- name    : RegevRecon.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:06:29.458476+00:00
-- url     : https://prove2.me/theorems/66038e82-2c7b-4378-a797-557619381a62
-- title:
--   Theorem 4 — $\beta_{\mathrm{BPQM}}=\beta_{\mathrm{dyn}}$, the law identities (54), and polynomial-time coherent Gibbs sampling below $\beta_{\mathrm{dyn}}$
-- statement:
--   Fix a prime $p$, integers $3\le k<D$, a nonempty proper subset $S\subsetneq\mathbb F_p$ and an exchangeable law $\Lambda$ on $(\mathbb F_p^\times)^D$, used for both recursions. Let $q^{(\ell)}\sim\mathcal Q_\ell$ be the BPQM messages and $\tilde\eta^{(\ell)}$ the reconstruction messages. Then:
--
--   1. for every finite $\beta\ge0$ and depth $\ell\ge0$,
--
--   $$
--   \tilde\eta^{(\ell)}\overset d=\mathcal L(q^{(\ell)}),\qquad\Psi_\ell=E\bigl[\|q^{(\ell)}-u\|_2^2\bigr];
--   $$
--
--   2. the thresholds coincide,
--
--   $$
--   \beta_{\mathrm{BPQM}}(k,D,p,S,\Lambda)=\beta_{\mathrm{dyn}}(k,D,p,S,\Lambda);
--   $$
--
--   3. for the finite-graph ensemble of Definition 2, every fixed $0\le\beta<\beta_{\mathrm{dyn}}$ admits polynomial-time coherent Gibbs sampling, with the error and failure guarantees of Corollary 3.
--
--   The theorem identifies BPQM decoding success with non-reconstruction on the tree, and it yields a polynomial-time quantum preparation of $|\psi_\beta\rangle$ up to the reconstruction threshold.
--
--   Differences from the source:
--   - reading: "by Regev+BPQM" / "Regev's reduction with the decoder of Proposition 2" → the existence of the polynomial-time algorithm, without naming BPQM in the clause; reason: the coherent finite-precision circuit, the order of the tree decodings and ℓ are specified only in [MPRP26, PR22], so the named algorithm cannot be pinned from this source; BPQM enters through the hypothesis on the recursion and the milestones
--   - reading: "polynomial-time" (the paper names no model) → a deterministic multi-stack Turing machine (Turing.TM2ComputableAux Bool Bool) writes a circuit over the finite gate set {H, T, CNOT} within C(n+1)^K steps, with at most C(n+1)^K gates and wires; reason: the paper names no machine or gate set; a fixed finite gate set is the strong reading, since gates with real parameters could carry the reals of the instance for free
--   - reading: every fixed real β, with no statement of how the algorithm knows β → the input word holds the binary digits of ⌊2ⁿβ⌋, and the machine may depend on β; reason: with no digits on the input the clause is false for uncomputable β, since the circuit would be a computable function of the instance; restricting to computable β would be a special case
--   - reading: "with probability 1 − o(1) over (B, τ) … within o(1) trace distance … failure probability o(1), as n → ∞" → one sequence ε_n → 0 chosen after p, k, D, S, Λ, β and M and before n, with probability ≥ 1 − ε_n that failure ≤ ε_n and trace distance ≤ ε_n; reason: this is the usual meaning of the three o(1) terms read with one common bound
--   - reading: "a state within o(1) trace distance of the coherent Gibbs state" → the accepted, normalized state on all wires is compared with |ψ_β⟩ ⊗ |flag = 1⟩ ⊗ |0⟩_work; reason: this is how (42) reads ("⟨ψ_β| ⊗ ⟨0|_work"); closeness on the x wires alone follows from it
--   - encoding: laws of random vectors, =d → finitely supported Law; =d is equality of masses at every whole vector; reason: all these vectors take finitely many values; same instances
--   - encoding: thresholds with inf ∅ = ∞ and lim > 0 → thresholds in ℝ≥0∞; lim > 0 is ¬Tendsto · atTop (𝓝 0); reason: for a nonnegative sequence with a limit the two agree, and the limits exist by milestones
-- source:
--   Jordan, Nguyen, Zhou, Regev's Reduction Reaches Reconstruction, STOC 2027 submission (manuscript sha256 9f861d6a…), Theorem 4, p.21 (informal version Theorem 1, p.5); proof pp.23–24

import Mathlib
import Definitions.Def_RegevRecon_qLaw
import Definitions.Def_RegevRecon_etaLaw
import Definitions.Def_RegevRecon_reconInfo
import Definitions.Def_RegevRecon_GibbsPreparable

namespace RegevRecon

/-- **Theorem 4 (Regev+BPQM reaches reconstruction threshold)**. Jordan, Nguyen, Zhou, *Regev's Reduction Reaches Reconstruction*, STOC 2027 submission (manuscript sha256 9f861d6a…), Theorem 4, p.21: fix a prime `p`, integers `3 ≤ k < D`,
a nonempty proper `S ⊊ F_p` and an exchangeable law `Λ` on `(F_p^×)^D`. For every finite `β ≥ 0` and depth `ℓ ≥ 0`,
`η̃^(ℓ) =d 𝓛(q^(ℓ))` and `Ψ_ℓ = E[‖q^(ℓ) − u‖₂²]` (54); `β_BPQM(k, D, p, S, Λ) = β_dyn(k, D, p, S, Λ)` (55); and for the finite-graph
ensemble of Definition 2, every fixed `0 ≤ β < β_dyn` admits polynomial-time coherent Gibbs sampling, with the error and failure
guarantees of Corollary 3.

**Formalization Note** Laws are `Law`s, so `=d` is equality of masses on whole vectors. `β_BPQM` is (52) and `β_dyn` is the
mutual-information form (46), both in `ℝ≥0∞`. `β` is any real: its digits are on the generator's input (`GibbsPreparable`), and the
polynomial-time clause asserts the existence of the algorithm, whose decoder is specified only in [MPRP26]. -/
theorem theorem_4 {p : ℕ} [Fact p.Prime] {k D : ℕ} (hk : 3 ≤ k) (hkD : k < D)
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hS' : S ≠ Finset.univ)
    (Λ : PMF (Fin D → (ZMod p)ˣ)) (hΛ : Exchangeable Λ) :
    (∀ β : ℝ, 0 ≤ β → ∀ ℓ : ℕ,
      etaLaw k D S Λ β ℓ = liftLaw (qLaw k D S Λ β ℓ) ∧
        Psi k D S Λ β ℓ = (qLaw k D S Λ β ℓ).expect distSq) ∧
    betaBPQM k D S Λ = betaDyn k D S Λ ∧
    ∀ β : ℝ, 0 ≤ β → ENNReal.ofReal β < betaDyn k D S Λ → GibbsPreparable k S Λ β := by sorry

end RegevRecon
