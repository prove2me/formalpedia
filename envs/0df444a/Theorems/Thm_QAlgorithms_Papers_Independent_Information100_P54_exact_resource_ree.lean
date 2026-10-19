-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P54_exact_resource_ree
-- name    : QAlgorithms.Papers.Independent.Information100.P54.exact_resource_ree
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:08:49.990424+00:00
-- url     : https://prove2.me/theorems/d6f17318-5593-47fd-85bd-bac49715a8e5
-- title:
--   Lemma 4 (Exact resource REE)
-- statement:
--   Let $0<\eta<1$, put $q=1-\eta$, and let $s\ge1$ and $m\ge0$ be integers. Write $d_{s,t}=\binom{s+t-1}{t}$ for the dimension of the $t$-photon sector of $s$ bosonic modes. Let $J_{s,m}$ be the state obtained by sending one share of the maximally entangled state of two $m$-photon sectors through $s$ parallel pure-loss channels of transmissivity $\eta$. Bob's total received photon number $K$ obeys
--
--   $$\Pr(K=k)=\binom{m}{k}\eta^kq^{m-k}\quad(0\le k\le m),\qquad \Pr(K=k)=0\quad(k>m).$$
--
--   For $0\le k\le m$, let $J_{s,m,k}$ be this resource conditioned on $K=k$. Across the reference:Bob cut, its relative entropy of entanglement in bits satisfies
--
--   $$E_R(J_{s,m,k})=\log_2\frac{d_{s,m}}{d_{s,m-k}},$$
--
--   and the unconditioned resource satisfies
--
--   $$E_R(J_{s,m})=F_{\eta,s}(m):=\log_2d_{s,m}-\mathbb E_{L\sim\operatorname{Bin}(m,q)}\log_2d_{s,L}.$$
--
--   Here $L=m-K$ counts lost photons, and $E_R(\rho)=\inf_{\sigma\in\mathrm{SEP}}D(\rho\Vert\sigma)$. These identities give the exact entanglement cost of each sector resource, including its received-number branches.
--
--   **Formalization Note** The resource is constructed by the number-basis vacuum loss dilation and a partial trace over the loss environment. Both parties use a finite occupation ambient space with zero padding outside the physical sectors; conditioning divides by the actual projector-trace probability.
-- source:
--   Energy-constrained two-way capacities of pure-loss and quantum-limited amplifier channels, arXiv:2610.06832v1, PDF p. 12, Lemma 4; Eqs.(B13)–(B15)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P54

noncomputable section

open scoped ENNReal Matrix

open Filter

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Information100.P54

/-- arXiv:2610.06832v1, PDF pp.12–13, Lemma 4, Eqs.(B13)–(B15).
The states are constructed from the loss dilation, not quantified by their claimed
REE. k is received and m-k is lost. The finite occupation ambient space only pads
zero rows and columns outside the physical sectors. s=1 and m=0 are included. -/
theorem exact_resource_ree (eta : ℝ) (heta0 : 0 < eta) (heta1 : eta < 1)
    (s m : ℕ) (hs : 1 ≤ s) :
    (∀ k : ℕ, receivedProbability eta s m k = binomialMass m eta k) ∧
    (∀ k : ℕ, k ≤ m →
      relativeEntanglement (conditionalSectorResource eta s m k) =
        ENNReal.ofReal (Real.log ((sectorDimension s m : ℝ) /
          (sectorDimension s (m - k) : ℝ)) / Real.log 2)) ∧
    relativeEntanglement (sectorResource eta s m) =
      ENNReal.ofReal (sectorCost eta s m) := by sorry

end QAlgorithms.Papers.Independent.Information100.P54

end
