-- Prove2me | Theorems.Thm_SampQueryLB_WarmSLC_lemma_4_5
-- name    : SampQueryLB.WarmSLC.lemma_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:17:06.657192+00:00
-- url     : https://prove2.me/theorems/0bb8e368-59f5-46ab-b394-f3cb2f58f192
-- title:
--   Lemma 4.5 — gate certificates and prefix oracle replies
-- statement:
--   Consider the hard family of §4.1. For a level $i$ write $A^\Xi_i=\prod_{j<i}G^\Xi_j$ and $V^\Xi_i-V^\Xi_{i-1}=A^\Xi_iU_i(\langle\Xi_i,\Phi_i\rangle)$.
--
--   **Lemma 4.5.** For every level $i$ and point $x$:
--   1. *Energy certificate.* If $G^\Xi_i(x)>0$ then $C_i(x)=1$ and $\big|\frac{\langle\Xi_{i,p},\Phi_{i,p}(x)\rangle}{na_{i,p}^2}+\beta_i\big|<\epsilon_g\beta_i$ for every $p\in\mathcal P$.
--   2. *Gate activation.* If $J(\|x_j\|/\sqrt n)=1$ for every $j\ge i$ and $\big|\frac{\langle\Xi_{i,p},\Phi_{i,p}(x)\rangle}{na_{i,p}^2}+\beta_i\big|\le\frac14\epsilon_g\beta_i$ for every $p$, then $G^\Xi_i(x)=1$.
--   3. *Inactive level.* If $A^\Xi_i(x)=0$ then $\nabla A^\Xi_i(x)=0$, and $V^\Xi_i$, $V^\Xi_{i-1}$ have the same value and gradient at $x$.
--   4. *Prefix simulation.* Given $\Xi_0,\dots,\Xi_{i-1}$, a joint value–gradient query to $V^\Xi_i$ at $x$ can be simulated by one joint query to $x\mapsto\langle\Xi_i,\Phi_i(x)\rangle$ when $A^\Xi_i(x)>0$; when $A^\Xi_i(x)=0$ no query to this function is needed.
--
--   In Lean, item 4 asserts a Borel map $\mathrm{sim}(\Xi,x,(s,g))$ depending on $\Xi$ only through $\Xi_{<i}$ with $\mathrm{sim}(\Xi,x,(H^\Xi_i(x),\nabla H^\Xi_i(x)))=(V^\Xi_i(x),\nabla V^\Xi_i(x))$ whenever $A^\Xi_i(x)>0$, and a Borel map $\mathrm{sim}_0(\Xi,x)$, depending only on $\Xi_{<i}$, equal to $(V^\Xi_i(x),\nabla V^\Xi_i(x))$ whenever $A^\Xi_i(x)=0$.
--
--   **Formalization Note.** The absolute constants $C_f, C_g, \eta_*, \lambda_*$ of the construction are quantified by `ForChosenConstants`: the statement holds for every $C_f\ge C_f^0$, then every $C_g\ge\max(1,C_g^0)$, then every $\eta_*\in(0,\min(1,\eta^0)]$, $\lambda_*\in(0,\min(1/2,\lambda^0)]$ with $\eta_*\lambda_*\le 1/4$ (the order and constraints of the proof of Proposition 4.2), and 'for all sufficiently large $n$' is $\exists n_0\,\forall n\ge n_0$. $V^\Xi_i$ is `Vpre c Ξ (i+1)` and $V^\Xi_{i-1}$ is `Vpre c Ξ i` (for $i=0$ this is $B$). The normalized energy $\langle\Xi_{i,p},\Phi_{i,p}(x)\rangle/(na_{i,p}^2)$ is `energy Ξ i p x`.
--
--   Differences from the source:
--   - reading: the absolute constants C_f, C_g, η*, λ* 'can be chosen' / are 'sufficiently large/small', n is 'a sufficiently large integer' (§4.1, proof of Proposition 4.2) → ForChosenConstants: the statement holds for all sufficiently extreme constants in the paper's choice order (C_f, then C_g ≥ 1, then η* ≤ 1, λ* ≤ 1/2, η*λ* ≤ 1/4), and for all n ≥ n0; reason: the paper fixes the constants once by monotone 'sufficiently' conditions; the for-all-sufficiently form implies the paper's existential choice and lets the thresholds of different results be combined
--   - encoding: x = (x_0, …, x_h) ∈ R^{d_n} with blocks x_j ∈ R^n; tensors in R^{n^{pS_i}} with ψ_i = u_i ⊗ u_{i+1}^{⊗K} ⊗ ⋯ → Point (dn n) with block j at coordinates finProdFinEquiv (j, a); G_n = EuclideanSpace on Σ (i,p), (Fin (p·S_i) → Fin n), slot r of ψ_i carrying block i + slotLevel K r; reason: a fixed labelling of coordinates and tensor slots; every statement is invariant under it
--   - encoding: 'a joint value–gradient query to V^Ξ_i at x can be simulated, given Ξ_0, …, Ξ_{i−1}, using one joint query to x ↦ ⟨Ξ_i, Φ_i(x)⟩' → ∃ a measurable map of (Ξ, x, reply) that depends on Ξ only through the blocks of levels < i and returns (V^Ξ_i(x), ∇V^Ξ_i(x)) from the reply (H^Ξ_i(x), ∇H^Ξ_i(x)) when A^Ξ_i(x) > 0; a second such map of (Ξ, x) alone when A^Ξ_i(x) = 0; reason: this is what simulation means in the oracle-simulation framework of §3.1 (Borel return maps)
-- source:
--   Zhou, Suzuki, Towards the Query Complexity of Sampling under Strong Log-Concavity and Log-Sobolev Inequalities, arXiv:2611.05813 (held version dated November 3, 2026, sha256 966f8fc0…184c), p. 32, Lemma 4.5 (PDF p. 35)

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_SampQueryLB_WarmSLC_Model
import Definitions.Def_SampQueryLB_WarmSLC_HardFamily
import Definitions.Def_SampQueryLB_WarmSLC_Experiments

open MeasureTheory OAI.LogConcaveSampling ProbabilityTheory Filter
open scoped ENNReal ContDiff RealInnerProductSpace Topology

namespace SampQueryLB.WarmSLC

theorem lemma_4_5 :
    ForChosenConstants fun c => ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ i : Lvl n,
      (∀ (Ξ : Coef n) (x : Point (dn n)), 0 < gate c Ξ i x →
        Ccut i x = 1 ∧ ∀ p : Deg n, |energy Ξ i p x + beta c n i| < epsG * beta c n i) ∧
      (∀ (Ξ : Coef n) (x : Point (dn n)),
        (∀ j : Lvl n, i ≤ j → Jcut (‖blk x j‖ / Real.sqrt n) = 1) →
        (∀ p : Deg n, |energy Ξ i p x + beta c n i| ≤ 1 / 4 * epsG * beta c n i) →
        gate c Ξ i x = 1) ∧
      (∀ (Ξ : Coef n) (x : Point (dn n)), gateProd c Ξ i x = 0 →
        gradient (gateProd c Ξ i) x = 0 ∧ Vpre c Ξ (i + 1) x = Vpre c Ξ i x ∧
        gradient (Vpre c Ξ (i + 1)) x = gradient (Vpre c Ξ i) x) ∧
      (∃ sim : Coef n × Point (dn n) × (ℝ × Point (dn n)) → ℝ × Point (dn n),
        Measurable sim ∧
        (∀ Ξ Ξ' : Coef n, (∀ k : CIdx n, k.1.1 < i → Ξ k = Ξ' k) →
          ∀ x r, sim (Ξ, x, r) = sim (Ξ', x, r)) ∧
        ∀ (Ξ : Coef n) (x : Point (dn n)), 0 < gateProd c Ξ i x →
          sim (Ξ, x, (field Ξ i x, gradient (field Ξ i) x)) =
            (Vpre c Ξ (i + 1) x, gradient (Vpre c Ξ (i + 1)) x)) ∧
      (∃ sim0 : Coef n × Point (dn n) → ℝ × Point (dn n),
        Measurable sim0 ∧
        (∀ Ξ Ξ' : Coef n, (∀ k : CIdx n, k.1.1 < i → Ξ k = Ξ' k) →
          ∀ x, sim0 (Ξ, x) = sim0 (Ξ', x)) ∧
        ∀ (Ξ : Coef n) (x : Point (dn n)), gateProd c Ξ i x = 0 →
          sim0 (Ξ, x) = (Vpre c Ξ (i + 1) x, gradient (Vpre c Ξ (i + 1)) x)) := by sorry

end SampQueryLB.WarmSLC
