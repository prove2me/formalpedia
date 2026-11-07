-- Prove2me | Theorems.Thm_RegevRecon_corollary_3
-- name    : RegevRecon.corollary_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:06:34.342959+00:00
-- url     : https://prove2.me/theorems/11615d6f-5a3d-4061-aa32-9b0e513dc27a
-- title:
--   Corollary 3 — coherent Gibbs sampling
-- statement:
--   Let $(B,F)\sim\mathbb G_{\mathrm{reg}}(n,k,D,p,S,\Lambda)$ and fix $\beta\ge0$. If the messages of density evolution satisfy $E[\|q^{(\ell)}-u\|_2^2]\to0$, then, with probability $1-o(1)$ over $(B,\tau)$, a state within $o(1)$ trace distance of $|\psi_\beta\rangle$ is prepared in polynomial time with failure probability $o(1)$, as $n\to\infty$. This applies to every exchangeable $\Lambda$, in particular to $\Lambda_{\mathrm{iid}}$ and $\Lambda_{\mathrm{perm}}$.
--
--   Differences from the source:
--   - reading: "by Regev+BPQM" / "Regev's reduction with the decoder of Proposition 2" → the existence of the polynomial-time algorithm, without naming BPQM in the clause; reason: the coherent finite-precision circuit, the order of the tree decodings and ℓ are specified only in [MPRP26, PR22], so the named algorithm cannot be pinned from this source; BPQM enters through the hypothesis on the recursion and the milestones
--   - reading: "polynomial-time" (the paper names no model) → a deterministic multi-stack Turing machine (Turing.TM2ComputableAux Bool Bool) writes a circuit over the finite gate set {H, T, CNOT} within C(n+1)^K steps, with at most C(n+1)^K gates and wires; reason: the paper names no machine or gate set; a fixed finite gate set is the strong reading, since gates with real parameters could carry the reals of the instance for free
--   - reading: every fixed real β, with no statement of how the algorithm knows β → the input word holds the binary digits of ⌊2ⁿβ⌋, and the machine may depend on β; reason: with no digits on the input the clause is false for uncomputable β, since the circuit would be a computable function of the instance; restricting to computable β would be a special case
--   - reading: "with probability 1 − o(1) over (B, τ) … within o(1) trace distance … failure probability o(1), as n → ∞" → one sequence ε_n → 0 chosen after p, k, D, S, Λ, β and M and before n, with probability ≥ 1 − ε_n that failure ≤ ε_n and trace distance ≤ ε_n; reason: this is the usual meaning of the three o(1) terms read with one common bound
--   - reading: "a state within o(1) trace distance of the coherent Gibbs state" → the accepted, normalized state on all wires is compared with |ψ_β⟩ ⊗ |flag = 1⟩ ⊗ |0⟩_work; reason: this is how (42) reads ("⟨ψ_β| ⊗ ⟨0|_work"); closeness on the x wires alone follows from it
--   - encoding: laws of random vectors, =d → finitely supported Law; =d is equality of masses at every whole vector; reason: all these vectors take finitely many values; same instances
-- source:
--   Jordan, Nguyen, Zhou, Regev's Reduction Reaches Reconstruction, STOC 2027 submission (manuscript sha256 9f861d6a…), Corollary 3, p.16; proof pp.16–17

import Mathlib
import Definitions.Def_RegevRecon_qLaw
import Definitions.Def_RegevRecon_GibbsPreparable

namespace RegevRecon

open Filter Topology

/-- **Corollary 3 (Coherent Gibbs sampling)**. Jordan, Nguyen, Zhou, *Regev's Reduction Reaches Reconstruction*, STOC 2027 submission (manuscript sha256 9f861d6a…), p.16: fix `β ≥ 0`; if the check-to-symbol messages of density
evolution satisfy `E[‖q^(ℓ) − u‖₂²] → 0`, then, with probability `1 − o(1)` over `(B, τ)`, a state within `o(1)` trace distance
of `|ψ_β⟩` is prepared in polynomial time with failure probability `o(1)`. It applies to every exchangeable `Λ`, including `Λ_iid`
and `Λ_perm` (verification file).

**Formalization Note** See `GibbsPreparable`, which asserts the existence of the polynomial-time algorithm: "Regev's reduction with
the decoder of Proposition 2" is not named in the clause, as the decoder is specified only in [MPRP26]. -/
theorem corollary_3 {p : ℕ} [Fact p.Prime] {k D : ℕ} (hk : 3 ≤ k) (hkD : k < D)
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hS' : S ≠ Finset.univ)
    (Λ : PMF (Fin D → (ZMod p)ˣ)) (hΛ : Exchangeable Λ)
    (β : ℝ) (hβ : 0 ≤ β)
    (h : Tendsto (fun ℓ => (qLaw k D S Λ β ℓ).expect distSq) atTop (𝓝 0)) :
    GibbsPreparable k S Λ β := by sorry

end RegevRecon
