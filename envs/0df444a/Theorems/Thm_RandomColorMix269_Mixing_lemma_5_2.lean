-- Prove2me | Theorems.Thm_RandomColorMix269_Mixing_lemma_5_2
-- name    : RandomColorMix269.Mixing.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:03:53.430212+00:00
-- url     : https://prove2.me/theorems/edc14639-39e8-4f5e-bcbb-0419e72fb218
-- title:
--   Lemma 5.2 — $T_{\mathrm{rel}}(P^{GD})\le nR\cdot T_{\mathrm{rel}}(\mathcal L_{\mathcal B})\cdot\max_v\sum_{B\ni v}w(B)$
-- statement:
--   Let $\mu$ be a probability distribution on $[q]^V$, $n=|V|\ge1$, and let $\mathcal B=\{B_1,\dots,B_r\}$ be a block cover of $V$ with update rates $w:\mathcal B\to\mathbb R_{>0}$. For each $i$ and each feasible pinning $\tau$ on $V\setminus B_i$ let $\mathcal L^\tau_i f=\sum_{v\in B_i}\big(\mathbb E_{\mu^\tau}[f\mid X(B_i\setminus\{v\})]-f\big)$. If there is $R>0$ with $T_{\mathrm{rel}}(\mathcal L^\tau_i)\le R$ for every $i$ and every such $\tau$, then
--   $$
--   T_{\mathrm{rel}}(P^{GD})\le nR\cdot T_{\mathrm{rel}}(\mathcal L_{\mathcal B})\cdot\max_{v\in V}\sum_{B\in\mathcal B:\,v\in B}w(B),
--   $$
--   where $P^{GD}=n^{-1}\sum_vK_v$ is the discrete single-site Glauber dynamics and $\mathcal L_{\mathcal B}=\sum_Bw(B)(K_B-I)$.
--
--   Differences from the source:
--   - encoding: spectral gap as an infimum over Var>0 and T_rel = 1/λ_gap with 1/0 = ∞ → infimum in ℝ≥0∞ (⊤ when no function has positive variance) and its inverse in ℝ≥0∞; reason: the source's convention; it avoids a real infimum of an empty set and a real inverse of 0
--   - generalization: a block cover as a set of blocks with rates → a finite indexed family of blocks (repetitions allowed) with positive rates; reason: a repeated block is the same as one block with the summed rate in both L_B and the overlap factor; sets are the special case of injective families
--   - encoding: vertex set V of size n → finite nonempty type V with n = |V|; reason: the overlap maximum needs V nonempty
--   - generalization: the standing convention of irreducible chains (p.27) → the global single-site and block chains may be disconnected; reason: heat-bath chains are automatically reversible, and if the block chain is disconnected the finite local relaxation bounds force the single-site chain to be disconnected too, giving ∞ ≤ ∞; the irreducible source case is included
--   - encoding: the pinned local chain is on B_i → the pinned law is kept on all of V with rate-one updates at every site; reason: sites outside B_i are fixed and have zero conditional variance, so the positive-variance Rayleigh quotient equals that of the source local chain
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #269 (October 2026), PDF sha256 467638f1abc0f57df1bc0dcd9abfd308eb90ddbaf4947dac3eefa5f293ac6f05, p.28, Lemma 5.2

import Definitions.Def_RandomColorMix269_Mixing_Entropy

open scoped Classical BigOperators
set_option autoImplicit false

namespace RandomColorMix269.Mixing

/-- Lemma 5.2, p.28. Arbitrary overlapping weighted covers, rate one per
vertex in each pinned block, versus one vertex per discrete step.
Extended relaxation also covers disconnected chains. -/
theorem lemma_5_2 {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {I : Type*} [Fintype I] {q : ℕ} (μ : (V → Fin q) → ℝ)
    (hμ : MarkovMixing.IsDist μ) (B : I → Finset V) (w : I → ℝ)
    (hcover : ∀ v : V, ∃ i : I, v ∈ B i) (hw : ∀ i : I, 0 < w i)
    (R : ℝ) (hR : 0 < R)
    (hlocal : ∀ (i : I) (x : V → Fin q), Feasible μ (B i)ᶜ x →
      singleRelaxation (SpinGirth5.pin μ (B i)ᶜ x) ≤ ENNReal.ofReal R) :
    discreteRelaxation μ ≤ ENNReal.ofReal ((Fintype.card V : ℝ) * R) *
      weightedRelaxation μ B w * ENNReal.ofReal (overlap B w) := by sorry

end RandomColorMix269.Mixing
