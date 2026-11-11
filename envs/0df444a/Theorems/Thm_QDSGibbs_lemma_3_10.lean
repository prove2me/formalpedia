-- Prove2me | Theorems.Thm_QDSGibbs_lemma_3_10
-- name    : QDSGibbs.lemma_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:38:53.248252+00:00
-- url     : https://prove2.me/theorems/2518c37f-cc37-4934-b095-dc75ea800752
-- title:
--   Lemma 3.10 — restriction estimates for $\mathcal F_H$ and $\mathcal G_H$ on chains
-- statement:
--   For a nearest-neighbour chain there are universal constants $c,C>0$ such that, with $\lambda=c/(1+\beta J_{\mathrm{int}})$: if $A$ is supported on a nonempty set $S$ and $S^{\le q}\subseteq\Omega\subseteq\Lambda$ with $q\ge0$, then
--
--   $$
--   \|\mathcal F_H(A)-\mathcal F_{H_\Omega}(A)\|\le C|S|\,\|A\|e^{-\lambda q},\qquad \|\mathcal G_H(A)-\mathcal G_{H_\Omega}(A)\|\le C\log(2+\beta J_{\mathrm{int}})\,|S|\,\|A\|e^{-\lambda q}.
--   $$
--
--   The same bounds hold for $H_{\Omega'}$ and $H_\Omega$ when $S\subseteq\Omega\subseteq\Omega'\subseteq\Lambda$ and $S^{\le q}\cap\Omega'\subseteq\Omega$.
--
--   These are the locality estimates that allow the QBP operators and coherent terms to be localized near the block boundary, uniformly in the on-site fields.
--
--   Differences from the source:
--   - reading: "universal constants" $c, C$ → constants chosen before the chain length, the local dimensions (any $d_i\ge2$), $\beta$ and the chain terms; reason: the paper's convention on p.39 ("$c, C$ denote universal positive constants")
--   - reading: constants ($C$, $c$, $C_d$) → constants required to be positive (and $c\le 1$ where $\lambda\le1$ is stipulated); reason: the paper's constants are positive by convention (p.39); a positive existential is the stronger reading
--   - encoding: sites $1,\dots,N$, bonds $W_i$ on $\{i,i+1\}$ → 0-based sites `Fin N`, bond `b : Fin (N−1)` on $\{b,b+1\}$; reason: a relabelling
--   - encoding: operators on a region $U$, partial traces $\mathrm{Tr}_S$, marginals and restricted Gibbs states acting on the subsystem → full-space matrices on $\prod_i \mathrm{Fin}\,d_i$: $A\otimes\mathbb 1$, `ptr S X` $=\mathbb 1_S\otimes\mathrm{Tr}_S X$, `gibbs β (hamOn I Ω)` $=\sigma^\Omega_\beta\otimes\mathbb 1/\dim$; reason: the paper extends operators by the identity in full-system expressions (p.10); norms, traces of products and covariances are unchanged
-- source:
--   Rouzé–Stilck França, Rapid mixing of Gibbs samplers via quantum Dobrushin–Shlosman conditions, arXiv:2610.03578 (held file sha256 ede55815…), Lemma 3.10, p.23

import Mathlib
import Definitions.Def_QDSGibbs_chainGen

open scoped Matrix

namespace QDSGibbs

/-- **Lemma 3.10** (arXiv:2610.03578, held file sha256 ede55815…, Lemma 3.10, p.23). For a
nearest-neighbour chain there are universal constants `c, C > 0` such that, with
`λ = c/(1 + βJ_int)`: if `A` is supported on a nonempty set `S` and `S^{≤q} ⊆ Ω ⊆ Λ`, `q ≥ 0`, then
`‖F_H(A) − F_{H_Ω}(A)‖ ≤ C|S|‖A‖e^{−λq}` (3.26) and
`‖G_H(A) − G_{H_Ω}(A)‖ ≤ C log(2 + βJ_int)|S|‖A‖e^{−λq}` (3.27). The same bounds hold for `H_{Ω′}`
and `H_Ω` when `S ⊆ Ω ⊆ Ω′ ⊆ Λ` and `S^{≤q} ∩ Ω′ ⊆ Ω`.

**Formalization Note** "Universal": `c, C` are chosen before the chain length, the local dimensions,
`β > 0` and the chain terms. `S^{≤q} = nbhd S q` with `dist(i, j) = |i − j|`; `H_Ω = hamOn`,
`J_int = jint (chain V W)`; `F = qbpF β`, `G = qbpG β`; `‖·‖` is the operator norm. -/
theorem lemma_3_10 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (N : ℕ) (d : Fin N → ℕ), (∀ i, 2 ≤ d i) →
        ∀ (V : Fin N → Op d) (W : Fin (N - 1) → Op d), IsChainHam V W → ∀ β : ℝ, 0 < β →
          ∀ S : Finset (Fin N), S.Nonempty → ∀ A : Op d, SupportedOn S A → ∀ q : ℝ, 0 ≤ q →
            (∀ Ω : Finset (Fin N), nbhd S q ⊆ Ω →
              opNorm (qbpF β (ham (chain V W)) A - qbpF β (hamOn (chain V W) Ω) A) ≤
                  C * S.card * opNorm A * Real.exp (-(c / (1 + β * jint (chain V W))) * q) ∧
              opNorm (qbpG β (ham (chain V W)) A - qbpG β (hamOn (chain V W) Ω) A) ≤
                  C * Real.log (2 + β * jint (chain V W)) * S.card * opNorm A *
                    Real.exp (-(c / (1 + β * jint (chain V W))) * q)) ∧
            (∀ Ω Ω' : Finset (Fin N), S ⊆ Ω → Ω ⊆ Ω' → nbhd S q ∩ Ω' ⊆ Ω →
              opNorm (qbpF β (hamOn (chain V W) Ω') A - qbpF β (hamOn (chain V W) Ω) A) ≤
                  C * S.card * opNorm A * Real.exp (-(c / (1 + β * jint (chain V W))) * q) ∧
              opNorm (qbpG β (hamOn (chain V W) Ω') A - qbpG β (hamOn (chain V W) Ω) A) ≤
                  C * Real.log (2 + β * jint (chain V W)) * S.card * opNorm A *
                    Real.exp (-(c / (1 + β * jint (chain V W))) * q)) := by sorry

end QDSGibbs
