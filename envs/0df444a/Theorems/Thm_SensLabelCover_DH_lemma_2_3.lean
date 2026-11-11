-- Prove2me | Theorems.Thm_SensLabelCover_DH_lemma_2_3
-- name    : SensLabelCover.DH.lemma_2_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:36:23.137193+00:00
-- url     : https://prove2.me/theorems/4a66380d-3c20-4e0c-a5fb-35e472ef3b88
-- title:
--   Lemma 2.3 — Fleming–Yoshida: swap-closed $d_0$-regular 2-CSP families on $N$ variables with $\mathrm{SwapSens}_{1-\eta_{src}}(\mathcal F_N)\ge N^{c_{src}}$
-- statement:
--   There are constants $\eta_{src},c_{src}\in(0,1)$, an even integer $d_0\ge2$ and a nonempty finite alphabet $\Sigma_{src}$ such that, for every sufficiently large $N$, there is a swap-closed family $\mathcal F_N$ of 2-CSPs on a common $d_0$-regular multigraph with $N$ variables and alphabet $\Sigma_{src}$ satisfying
--   $$\mathrm{SwapSens}_{1-\eta_{src}}(\mathcal F_N)\ge N^{c_{src}}:$$
--   every algorithm (a map from instances to distributions over assignments) whose output has expected value at least $1-\eta_{src}$ on every satisfiable member of $\mathcal F_N$ has some member $R$ and some one-relation swap $R'$ of it with $\mathrm{EMD}(A(R),A(R'))\ge N^{c_{src}}$.
--
--   This cited bound ([18] in the paper, padded to every $N$) is the source of the sensitivity that the paper transfers to low-soundness Label Cover.
--
--   Differences from the source:
--   - encoding: $\mathrm{SwapSens}_s(\mathcal F)$, the minimum over algorithms with the value guarantee of their swap sensitivity → "every algorithm with the guarantee has a member and a swap with EMD at least $N^{c_{src}}$"; reason: there are finitely many instances, so the maximum is attained, and an algorithm with the guarantee exists.
--   - encoding: variables, edges and alphabet → `Fin N`, `Fin m`, `Fin s` with $s\ge1$; "sufficiently large $N$" → $N\ge N_0$; regularity counts endpoint incidences; reason: Lean convention, same instances. An alphabet is nonempty.
-- source:
--   Fleming, Hopkins, Yoshida, Sensitivity and Locality Lower Bounds via Low-Soundness Label Cover, STOC 2027 submission (manuscript sha256 5bfe95ad…), p. 16 (PDF 19), Lemma 2.3

import Mathlib
import Definitions.Def_SensLabelCover_DH_TwoCSP

namespace SensLabelCover.DH

/-- Lemma 2.3 (Fleming–Yoshida sensitivity lower bound), p. 16 (PDF p. 19). Variables are
`Fin N`, edges `Fin m`, the alphabet `Σ_src` is `Fin s` (`s ≥ 1`). `SwapSens_{1−η_src}(𝓕_N) ≥
N^{c_src}` is stated for every algorithm with the value guarantee on satisfiable members: some
member and some one-relation swap of it have EMD at least `N^{c_src}` (a maximum over the finitely
many instances). -/
theorem lemma_2_3 :
    ∃ ηsrc csrc : ℝ, 0 < ηsrc ∧ ηsrc < 1 ∧ 0 < csrc ∧ csrc < 1 ∧
      ∃ d₀ : ℕ, Even d₀ ∧ 2 ≤ d₀ ∧ ∃ s : ℕ, 0 < s ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∃ (m : ℕ) (G : CSPGraph (Fin N) (Fin m)) (𝓕 : Set (CSPInst (Fin m) (Fin s))),
          (∀ x, G.deg x = d₀) ∧ SwapClosed cspAdj 𝓕 ∧
          ∀ A : CSPInst (Fin m) (Fin s) → PMF (Fin N → Fin s),
            (∀ R ∈ 𝓕, cspSat G R → 1 - ηsrc ≤ expect (A R) (cspVal G R)) →
            ∃ R ∈ 𝓕, ∃ R', cspAdj R R' ∧ (N : ℝ) ^ csrc ≤ emd cspDist (A R) (A R') := by sorry

end SensLabelCover.DH
