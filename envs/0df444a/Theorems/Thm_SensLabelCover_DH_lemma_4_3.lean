-- Prove2me | Theorems.Thm_SensLabelCover_DH_lemma_4_3
-- name    : SensLabelCover.DH.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:37:23.694192+00:00
-- url     : https://prove2.me/theorems/04535ad7-b911-4f5a-99f8-b36fb7fa20c2
-- title:
--   Lemma 4.3 — right-degree reduction: satisfiability, $\mathrm{val}_{T_{DR}}(\pi')\le\mathbb E\,\mathrm{val}_I(R_{DR}(\pi'))+\lambda$, and couplings transfer with factors $d$ and $d/\delta_V$
-- statement:
--   Let $d\ge6$ be even and $\lambda\in[0,1)$. Let $\mathcal I$ be a swap-closed family of left-predicate Label Cover instances on a common graph $G=(U,V,E)$ and alphabets, with minimum right degree $\delta_V\ge1$. For each right vertex $v$ fix a $[D_v,d,\lambda]$-expander and an ordering of the edges at $v$, and put $\mathcal I'=\mathrm{SwapClo}(T_{DR}(\mathcal I;d))$. Then:
--   1. every right vertex of the reduced graph has degree $d$, and $T_{DR}$ maps satisfiable members of $\mathcal I$ to satisfiable instances;
--   2. for every $I\in\mathcal I$ and every assignment $\pi'$ of $T_{DR}(I;d)$,
--   $$\mathrm{val}_{T_{DR}(I;d)}(\pi')\le\mathbb E\big[\mathrm{val}_I(R_{DR,I}(\pi'))\big]+\lambda;$$
--   3. for every $\varepsilon>0$ and every algorithm $A'$ on $\mathcal I'$ whose output has expected value at least $\varepsilon+\lambda$ on every satisfiable member, the algorithm $A(I):=R_{DR,I}(A'(T_{DR}(I;d)))$ has expected value at least $\varepsilon$ on every satisfiable member of $\mathcal I$. Moreover, if for all neighbouring $J,\tilde J\in\mathcal I'$ there is one coupling $(\pi',\tilde\pi')$ of $A'(J),A'(\tilde J)$ with $\mathbb E[d_H(\pi'_U,\tilde\pi'_U)]\le x_U$ and $\mathbb E[d_H(\pi'_V,\tilde\pi'_V)]\le x_V$, then for all neighbouring $I,\tilde I\in\mathcal I$ there is a coupling $(\pi,\tilde\pi)$ of $A(I),A(\tilde I)$ with
--   $$\mathbb E[d_H(\pi_U,\tilde\pi_U)]\le d\,x_U,\qquad \mathbb E[d_H(\pi_V,\tilde\pi_V)]\le\frac d{\delta_V}\,x_V .$$
--
--   Degree reduction thus preserves completeness, loses only $\lambda$ in soundness, and multiplies sensitivity by at most $d$ on the left and $d/\delta_V$ on the right.
--
--   Differences from the source:
--   - generalization: $[D_v,d,\lambda]$-expanders of Definition 4.1 → neighbour functions with symmetric incidence counts and $\|E_\Gamma-U\|\le\lambda$ (the published `SmallBiasPRF` definitions), which also admit an odd number of loop incidences; reason: every expander of Definition 4.1 is one, so the statement specializes to the paper's.
--   - encoding: the family on a common graph and alphabets → a fixed `BGraph U V E` and a swap-closed set of $(P,F)$ on it; $\delta_V\ge1$ → no isolated right vertex, with $\delta_V$ the minimum right degree; reason: same instances.
--   - encoding: $[D_v]$ and the incidence ordering → `Fin D_v` (0-based) and a bijection with the edges at $v$; reason: Lean convention.
--   - encoding: random labelings, couplings and $A(I)$ → PMFs, a PMF on pairs with the two marginals, and `(A' (T_DR I)).bind R_DR`; reason: same objects on finite sets.
-- source:
--   Fleming, Hopkins, Yoshida, Sensitivity and Locality Lower Bounds via Low-Soundness Label Cover, STOC 2027 submission (manuscript sha256 5bfe95ad…), p. 23 (PDF 26), Lemma 4.3

import Mathlib
import Definitions.Def_SensLabelCover_DH_DegreeReduction

namespace SensLabelCover.DH

/-- Lemma 4.3 (Sensitivity transfer through right-degree reduction), p. 23 (PDF p. 26). The
family `𝓘` lives on the fixed graph `G` with no isolated right vertex (`δ_V ≥ 1`); `dr` holds a
`[D_v, d, λ]`-expander and an incidence ordering at each right vertex `v`. `𝓘' = SwapClo(T_DR(𝓘; d))`,
and `A(I) := R_DR,I(A'(T_DR(I; d)))`. -/
theorem lemma_4_3 {U V E SU SV : Type} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] [Fintype SU] [DecidableEq SU] [Fintype SV] [DecidableEq SV]
    (G : BGraph U V E) (d : ℕ) (hd6 : 6 ≤ d) (hdeven : Even d) (lam : ℝ) (hlam0 : 0 ≤ lam)
    (hlam1 : lam < 1) (𝓘 : Set (LCInst U E SU SV)) (h𝓘 : SwapClosed lcAdj 𝓘)
    (hD : ∀ v, 0 < G.rdeg v) (dr : DRData G d) (hexp : ∀ v, IsExpander (dr.nb v) lam) :
    (∀ x : DRV G, (drGraph dr).rdeg x = d) ∧
      (∀ I ∈ 𝓘, lcSat G I → lcSat (drGraph dr) (tdr dr I)) ∧
      (∀ I ∈ 𝓘, ∀ π' : Assignment U (DRV G) SU SV,
        lcVal (drGraph dr) (tdr dr I) π' ≤ expect (recoverDR G hD π') (lcVal G I) + lam) ∧
      ∀ ε : ℝ, 0 < ε →
        ∀ A' : LCInst U (DRE G d) SU SV → PMF (Assignment U (DRV G) SU SV),
          (∀ J ∈ swapClo lcAdj (tdr dr '' 𝓘), lcSat (drGraph dr) J →
              ε + lam ≤ expect (A' J) (lcVal (drGraph dr) J)) →
          (∀ I ∈ 𝓘, lcSat G I →
              ε ≤ expect ((A' (tdr dr I)).bind (recoverDR G hD)) (lcVal G I)) ∧
          ∀ xU xV : ℝ,
            (∀ J ∈ swapClo lcAdj (tdr dr '' 𝓘), ∀ J', lcAdj J J' →
                ∃ γ, IsCoupling (A' J) (A' J') γ ∧
                  expect γ (fun p => (hammingDist p.1.1 p.2.1 : ℝ)) ≤ xU ∧
                  expect γ (fun p => (hammingDist p.1.2 p.2.2 : ℝ)) ≤ xV) →
            ∀ I ∈ 𝓘, ∀ I', lcAdj I I' →
              ∃ γ, IsCoupling ((A' (tdr dr I)).bind (recoverDR G hD))
                  ((A' (tdr dr I')).bind (recoverDR G hD)) γ ∧
                expect γ (fun p => (hammingDist p.1.1 p.2.1 : ℝ)) ≤ (d : ℝ) * xU ∧
                expect γ (fun p => (hammingDist p.1.2 p.2.2 : ℝ)) ≤
                  ((d : ℝ) / (G.minRDeg : ℝ)) * xV := by sorry

end SensLabelCover.DH
