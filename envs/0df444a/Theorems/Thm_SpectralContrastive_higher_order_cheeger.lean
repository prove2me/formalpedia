-- Prove2me | Theorems.Thm_SpectralContrastive_higher_order_cheeger
-- name    : SpectralContrastive.higher_order_cheeger
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T18:36:47.307818+00:00
-- url     : https://prove2.me/theorems/988a7530-412a-42a2-9b59-8c265a1f63e9
-- title:
--   Lemma B.4: higher-order Cheeger inequality (Louis and Makarychev)
-- statement:
--   There are universal constants $C$ and $K$ with the following property. Let $G=(V,w)$ be a finite weighted graph, with nonnegative symmetric weights and positive degrees, and let $|V|=N$. Let $\lambda_s$ be the $s$-th smallest eigenvalue of its normalized Laplacian. For any integer $t\ge1$ and real $\zeta>0$ such that $s=(1+\zeta)t$ is an integer with $s\le N$, there is a partition of $V$ into nonempty sets $S_1,\dots,S_t$ with
--
--   $$\phi_G(S_i)\le C\,(1+1/\zeta)^K\sqrt{\lambda_{(1+\zeta)t}\log t}\qquad(i=1,\dots,t).$$
--
--   This is the higher-order Cheeger inequality of Louis and Makarychev (2014), as quoted in the paper. It converts the eigenvalue $\lambda_{k+1}$ into the sparsest partition $\rho_{k'}$.
--
--   **Formalization Note** The paper writes $\phi_G(S_i)\lesssim\mathrm{poly}(1/\zeta)\sqrt{\lambda_{(1+\zeta)t}\log t}$. Every polynomial in $1/\zeta$ is bounded by $C(1+1/\zeta)^K$, so the universal polynomial is written in that form. The sets of the partition are nonempty, which is how the lemma is used with Definition 3.4.
-- source:
--   HaoChen, Wei, Gaidon and Ma, Provable Guarantees for Self-Supervised Deep Learning with Spectral Contrastive Loss, arXiv:2106.04156v7 (NeurIPS 2021), Appendix B.1, Lemma B.4 (Proposition 1.2 of Louis and Makarychev 2014), p. 27

import Mathlib
import Definitions.Def_SpectralContrastive_Basic

open Matrix

namespace SpectralContrastive

theorem higher_order_cheeger :
    ∃ (C : ℝ) (K : ℕ), ∀ (V : Type) [Fintype V] [DecidableEq V] (w : V → V → ℝ),
      IsWeightedGraph w → ∀ (t s : ℕ) (ζ : ℝ), 0 < ζ → 1 ≤ t → (1 + ζ) * (t : ℝ) = s →
      s ≤ Fintype.card V →
      ∃ σ : V → Fin t, Function.Surjective σ ∧ ∀ i : Fin t,
        conductance w (Finset.univ.filter fun x => σ x = i) ≤
          C * (1 + 1 / ζ) ^ K * Real.sqrt (lapEig w s * Real.log t) := by sorry

end SpectralContrastive
