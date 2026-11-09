-- Prove2me | Theorems.Thm_TestingEstimation_Dense_label_encoding
-- name    : TestingEstimation.Dense.label_encoding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:13:50.268195+00:00
-- url     : https://prove2.me/theorems/9da7e717-26ae-4d30-a5ee-14cea4c13e24
-- title:
--   Lemma 4 — vertex-label approximation and decoder locality
-- statement:
--   Fix a sample size $s=a+2\ge2$, an order $n\ge s$, a symmetric rational rule $f$, and real $0<\gamma<1$. Let $T(G)$ and the finite alphabet $\Lambda=(C\times\Omega)^{\lceil\gamma^{-2}\rceil}$ be the derivative-test and label constructions. For every ordinary graph $G$ and every weighted graph $H$, there is a vertex labeling $z:V\to\Lambda$ such that
--
--   $$\|H-W_z\|_{T(G)}\le\gamma.$$
--
--   Moreover, for every labeling, including inconsistent ones,
--
--   $$W_z(uv)=D(G(uv),z_u,z_v).$$
--
--   Locality is also explicit as an invariance assertion: changing $G$ or labels anywhere else cannot change this decoded edge if its input bit and two endpoint labels agree. The good labeling is existential; it is not supplied to an estimator. The formula expresses why this finite description can be evaluated using sampled edges.
--
--   Differences from the source:
--   - encoding: graphs on arbitrary finite vertex sets and uniform unordered-pair or ordered-injective-tuple averages → graphs on Fin n, increasing endpoint pairs, and exact finite averages; reason: enumeration and relabeling preserve every finite instance and the source normalization
--   - encoding: sample size s at least 2 with anchors [3,s] → s=a+2 with anchors Fin a; reason: this bijective reindexing includes s=2 and its empty anchor set
--   - generalization: f is the symmetric rational canonical rule furnished by Proposition 1, including (N2) → f is any symmetric rational rule with values in [0,1], without an (N2) premise; reason: these analytic conclusions use only the rule table and its symmetry, so every source canonical rule is included
--   - encoding: the decoded edge depends only on its original bit and two endpoint labels → the decoder equation plus explicit invariance when these three inputs agree; reason: this spells out locality without any extra oracle access
-- source:
--   Gaia Carenini, Cameron Seth, STOC 2027 submission #583 (October 2026), Lemma 4, p. 15 (PDF 15)

import Definitions.Def_TestingEstimation_Dense_Labels

noncomputable section

namespace TestingEstimation.Dense

theorem label_encoding {a n : ℕ} (hn : a+2 ≤ n) (f : Rule (a+2))
    (hf : SymmetricRule f) (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 1)
    (G : Graph n) (H : WGraph n) :
    (∃ z : Fin n → Label a γ,
      correlation (tests f G) (values H - values (decoded f γ G z)) ≤ γ) ∧
    (∀ (z : Fin n → Label a γ) (e : Edge n),
      decoded f γ G z e = decoder f γ (G e) (z e.val.1) (z e.val.2)) ∧
    (∀ (G' : Graph n) (z z' : Fin n → Label a γ) (e : Edge n),
      G e = G' e → z e.val.1 = z' e.val.1 → z e.val.2 = z' e.val.2 →
      decoded f γ G z e = decoded f γ G' z' e) := by sorry

end TestingEstimation.Dense
