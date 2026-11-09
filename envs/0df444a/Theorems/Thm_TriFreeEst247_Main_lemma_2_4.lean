-- Prove2me | Theorems.Thm_TriFreeEst247_Main_lemma_2_4
-- name    : TriFreeEst247.Main.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:11:50.027047+00:00
-- url     : https://prove2.me/theorems/36146155-9af9-4374-9b88-16c75ce13cc1
-- title:
--   Lemma 2.4: short-label compression with a local rule
-- statement:
--   There is an absolute $C_A>0$ such that for all $\lambda\ge0$ and $0<\eta<1/10$, the concrete alphabet $A_{\lambda,\eta}$ of Definition 3.1 satisfies
--
--   $$\log|A_{\lambda,\eta}|\le C_A(1+\lambda)^2\eta^{-3}.$$
--
--   There is a rule, chosen before the input graph and depending only on $\lambda,\eta,n$, that computes the entire local function from the three adjacency bits. For every $n\ge3$ and every graph $G$, the concrete $Q_G$ of Definition 3.2 is dense and normalized and satisfies
--
--   $$\mathrm{OPT}_\lambda(G)\le(1+\lambda)(1-\mathrm{OPT}_{\mathrm{CSP}}(Q_G))\le\mathrm{OPT}_\lambda(G)+\eta.$$
--
--   The alphabet is independent of $n,G$ and the rule is independent of $G$. This includes the locality condition as well as the size bound and both sides of the approximation.
--
--   Differences from the source:
--   - encoding: finite graphs and their vertex sets → simple graphs on Fin n, with unordered edges and triangles; reason: relabeling preserves every source instance and all normalized quantities
--   - reading: log |Aλ,η| = O((1+λ)²η⁻³) → one absolute positive C_A, using the natural logarithm; reason: the polynomial and O constants are absolute and quantified before every varying parameter
--   - generalization: existence of an alphabet and local CSP with the stated properties → the particular alphabet and graph CSP of Definitions 3.1–3.2 have those properties; reason: the proof constructs precisely these objects, so this implies the printed existential statement
--   - encoding: colors and blocks in Definitions 3.1–3.2 → 0-based finite indices; reason: the identical labels and local rule are obtained by renumbering block coordinates
-- source:
--   Asaf Shapira, Nick Kushnir, Triangle-Freeness: Estimation Is as Easy as Testing, STOC 2027 submission #247 (October 2026), source.pdf SHA-256 c24a6ad41f5c2465027e143e0aa757c3288add8cceb703078b9c0c2e18a0c3ad, p.8, Lemma 2.4

import Mathlib
import Definitions.Def_TriFreeEst247_Main_LabelConstruction

open scoped ENNReal

namespace TriFreeEst247.Main

theorem lemma_2_4 :
    ∃ C : ℝ, 0 < C ∧ ∀ lam η : ℝ, 0 ≤ lam → 0 < η → η < 1 / 10 →
      Real.log (Fintype.card (Label lam η) : ℝ) ≤ C * (1 + lam)^2 * η⁻¹^3 ∧
      ∃ rule : ℕ → Bool → Bool → Bool → Label lam η → Label lam η → Label lam η → ℝ,
        ∀ n, 3 ≤ n → ∀ G : Graph n,
          isDense (graphCSP G lam η) ∧
          (scoreOpt G lam ≤ (1 + lam) * (1 - cspOpt (graphCSP G lam η)) ∧
            (1 + lam) * (1 - cspOpt (graphCSP G lam η)) ≤ scoreOpt G lam + η) ∧
          ∀ x y z, distinct3 x y z →
            graphCSP G lam η x y z =
              rule n (graphOracle G (x,y)) (graphOracle G (y,z)) (graphOracle G (z,x))
    := by sorry

end TriFreeEst247.Main
