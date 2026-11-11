-- Prove2me | Theorems.Thm_RandomColorMix269_Mixing_lemma_5_16
-- name    : RandomColorMix269.Mixing.lemma_5_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:04:46.386728+00:00
-- url     : https://prove2.me/theorems/b3931e7d-0ec3-4ed4-922b-b029635a0e56
-- title:
--   Lemma 5.16 — $\lambda_{\mathrm{gap}}(\mathcal L_{\mathcal B})=\min\{|U|,\lambda_{\mathrm{gap}}(\mathcal L_\nu)\}$ and $T_{\mathrm{rel}}(\mathcal L_{\mathcal B})\le C_{LD}$
-- statement:
--   Let $G$ be a finite $q$-colourable graph, $D$ a cutoff with $q\ge5$ and $q-D\ge3$, $S=N_G[V^{HD}]$, $U=V\setminus S$, $\mu=\mu_{G,q}$, $\nu=\mu_U$, and $\mathcal L_{\mathcal B}=\sum_{u\in U}(P_u-I)$ with $P_uf=\mathbb E_\mu[f\mid X(U\setminus\{u\})]$. Then
--   $$
--   \lambda_{\mathrm{gap}}(\mathcal L_{\mathcal B})=\min\{|U|,\lambda_{\mathrm{gap}}(\mathcal L_\nu)\},
--   $$
--   where $\mathcal L_\nu$ is the continuous-time single-site Glauber dynamics for $\nu$, and the $|U|$ branch is omitted when the subspace $H=\{h:\mathbb E_\mu[h\mid X(U)]=0\}$ is zero. Consequently, when $U\ne\emptyset$, for every $C_{LD}>0$ such that $\nu$ satisfies the single-site entropy factorization of Proposition 5.15 with constant $C_{LD}$,
--   $$
--   T_{\mathrm{rel}}(\mathcal L_{\mathcal B})\le C_{LD}.
--   $$
--
--   Differences from the source:
--   - encoding: spectral gap as an infimum over Var>0 and T_rel = 1/λ_gap with 1/0 = ∞ → infimum in ℝ≥0∞ (⊤ when no function has positive variance) and its inverse in ℝ≥0∞; reason: the source's convention; it avoids a real infimum of an empty set and a real inverse of 0
--   - generalization: the buffer of G ∼ G(n,d/n) under the §5.2 standing assumptions q − D ≥ 3, q ≥ 5 → any finite q-colourable graph and any cutoff D with q ≥ 5 and q ≥ D + 3; reason: the identity and its proof are deterministic; it specializes to the source's graph
--   - reading: 'consequently T_rel(L_B) ≤ C_LD assuming Proposition 5.15' → for U ≠ ∅ and every C_LD > 0 with which ν satisfies the entropy factorization; reason: the proof (p.36) argues 'When U ≠ ∅'; for U = ∅ and a non-singleton colouring support, L_B = 0 has infinite relaxation time; on a singleton support it has relaxation time 0; U ≠ ∅ holds w.h.p. by Proposition 5.11
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #269 (October 2026), PDF sha256 467638f1abc0f57df1bc0dcd9abfd308eb90ddbaf4947dac3eefa5f293ac6f05, p.36, Lemma 5.16

import Definitions.Def_RandomColorMix269_Mixing_Parameters

open scoped Classical BigOperators ENNReal
set_option autoImplicit false

namespace RandomColorMix269.Mixing

/-- Lemma 5.16, p.36, equality and relaxation consequence. Positive variance
is interpreted in L² of the support; a zero-dimensional residual subspace
omits the |U| branch. The singleton marginal gap is ∞, not zero. -/
theorem lemma_5_16 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (q D : ℕ) (hq : 5 ≤ q) (hslack : D + 3 ≤ q)
    (hcol : Colorable G q) :
    let μ := MarkovMixing.properColoringDist G q
    let U := lowRegion G D
    let ν := bufferedLaw G q D
    variationalGap μ (bufferEnergy G q D) =
      (if ResidualNonzero μ U then
        min (U.card : ℝ≥0∞) (variationalGap ν (singleEnergy ν))
       else variationalGap ν (singleEnergy ν)) ∧
      (U.Nonempty → ∀ CLD : ℝ, 0 < CLD → SingleFactorization ν CLD →
        relaxation μ (bufferEnergy G q D) ≤ ENNReal.ofReal CLD) := by sorry

end RandomColorMix269.Mixing
