-- Prove2me | Theorems.Thm_TestingEstimation_Dense_csp_identity
-- name    : TestingEstimation.Dense.csp_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:14:30.431917+00:00
-- url     : https://prove2.me/theorems/dbbedf86-2a57-4550-9ed4-6b65c3866e4d
-- title:
--   Lemma 5 — loss identity and collision-normalized CSP optimum
-- statement:
--   Fix $s=a+2\ge2$, $n\ge s$, a symmetric rational rejection rule $f$, and real $0<\gamma<1$. For an ordinary graph $G$, form the local loss $\ell_v$ and the ordered dense CSP $I(G)$ using the same rule, decoder and alphabet on every restriction. For every labeling $z:V\to\Lambda$,
--
--   $$\mathbb E_{v\in V^s_{\ne}}\ell_v(z_{v_1},\ldots,z_{v_s})=E_G(W_z).$$
--
--   Consequently, with $a_n=(n)_s/n^s$,
--
--   $$\operatorname{OPT}(I(G))=a_n\left(1-\frac{\widetilde M(G)}3\right).$$
--
--   The codomain assertions in the construction are explicit: every loss lies in $[0,3]$, every payoff $1-\ell_v/3$ lies in $[0,1]$, and the full CSP maximum is attained. Uniform injective averaging occurs in the first equality, while the CSP is normalized by $n^s$. The collision factor is essential to their exact relationship.
--
--   Differences from the source:
--   - encoding: graphs on arbitrary finite vertex sets and uniform unordered-pair or ordered-injective-tuple averages → graphs on Fin n, increasing endpoint pairs, and exact finite averages; reason: enumeration and relabeling preserve every finite instance and the source normalization
--   - encoding: sample size s at least 2 with anchors [3,s] → s=a+2 with anchors Fin a; reason: this bijective reindexing includes s=2 and its empty anchor set
--   - encoding: minimum or maximum → real infimum or supremum together with an explicit IsLeast or IsGreatest conclusion; reason: the conclusion includes attainment and excludes a replacement by a merely unattained extremal value
--   - generalization: f is the symmetric rational canonical rule furnished by Proposition 1, including (N2) → f is any symmetric rational rule with values in [0,1], without an (N2) premise; reason: these analytic conclusions use only the rule table and its symmetry, so every source canonical rule is included
--   - encoding: losses and predicates have codomains [0,3] and [0,1] → real-valued tables with explicit universal bounds in the conclusion; reason: these bounds are proof obligations rather than assumptions hidden in a definition
-- source:
--   Gaia Carenini, Cameron Seth, STOC 2027 submission #583 (October 2026), Lemma 5, p. 16 (PDF 16)

import Definitions.Def_TestingEstimation_Dense_CSP

noncomputable section

namespace TestingEstimation.Dense

theorem csp_identity {a n : ℕ} (hn : a+2 ≤ n) (f : Rule (a+2))
    (hf : SymmetricRule f) (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 1) (G : Graph n) :
    (∀ z : Fin n → Label a γ,
      mean (fun v : Fin (a+2) ↪ Fin n => tupleLoss f γ G v (fun i => z (v i))) =
        energy f G (decoded f γ G z)) ∧
    optimum (graphInstance f γ G) = collisionFactor n (a+2) * (1 - labelMinimum f γ G / 3) ∧
    (∀ v ζ, 0 ≤ tupleLoss f γ G v ζ ∧ tupleLoss f γ G v ζ ≤ 3) ∧
    PayoffsIn01 (graphInstance f γ G) ∧
    IsGreatest (Set.range (cspScore (graphInstance f γ G) Finset.univ))
      (optimum (graphInstance f γ G)) := by sorry

end TestingEstimation.Dense
