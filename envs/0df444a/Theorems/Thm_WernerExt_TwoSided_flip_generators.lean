-- Prove2me | Theorems.Thm_WernerExt_TwoSided_flip_generators
-- name    : WernerExt.TwoSided.flip_generators
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:43:26.183036+00:00
-- url     : https://prove2.me/theorems/135b2014-9b17-4327-af5c-9d35caba0f32
-- title:
--   SM Eq. (6), Supplemental Material p. 1 — the flip in su(d) generators: F_ij = Σ_{α,β} S^{αβ}_i S^{βα}_j + 𝟙/d
-- statement:
--   Let $d\ge2$ and $S^{\alpha\beta}=|\beta\rangle\langle\alpha|-\frac1d\delta_{\beta\alpha}\mathbb 1$ ($\alpha,\beta=1,\dots,d$) be the $\mathfrak{su}(d)$ generators. Then
--
--   1. on two $d$-level sites, $$F=\sum_{\alpha,\beta=1}^dS^{\alpha\beta}\otimes S^{\beta\alpha}+\frac{\mathbb 1}{d};$$
--   2. on the joint system, for every Alice site $i$ and Bob site $j$, $$F_{ij}=\sum_{\alpha,\beta=1}^dS^{\alpha\beta}_iS^{\beta\alpha}_j+\frac{\mathbb 1}{d},$$ where $S_i$ acts on Alice's site $i$ and $S_j$ on Bob's site $j$.
--
--   This identity rewrites the Hamiltonian $H^W$ through quadratic Casimir operators (Eq. (5)).
--
--   **Formalization Note** The basis of $\mathbb C^d$ is indexed by `Fin d`.
--
--   Differences from the source:
--   - encoding: F_ij on two tensor components of an n-fold product → clause 1, the identity on two sites, and clause 2, its embedding at Alice's site i and Bob's site j of the joint system; reason: (6) is an identity of operators on two tensor factors; clause 2 is the embedding the mission uses
--   - encoding: basis |1⟩, …, |d⟩ → basis indexed by Fin d; reason: Lean indexing convention; same instances
-- source:
--   Jakab, Solymos, Zimborás, Extendibility of Werner States, arXiv:2208.13743v2, Supplemental Material p. 1 (PDF 7), SM Eq. (6)

import Mathlib
import Definitions.Def_WernerExt_TwoSided_Model

namespace WernerExt.TwoSided

open Matrix
open scoped Kronecker ComplexOrder

/-- SM Eq. (6), SM p. 1: the flip in terms of the `su(d)` generators,
`F_ij = ∑_{α,β} S^{αβ}_i S^{βα}_j + 𝟙/d`, (a) on two `d`-level sites and (b) for Alice's site
`i` and Bob's site `j` of the joint system. -/
theorem flip_generators (d : ℕ) (hd : 2 ≤ d) :
    flip d = ∑ a : Fin d, ∑ b : Fin d, (gen d a b ⊗ₖ gen d b a) +
        ((d : ℂ)⁻¹) • (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ∧
      ∀ (nA nB : ℕ) (i : Fin nA) (j : Fin nB),
        flipAB (d := d) i j =
          ∑ a : Fin d, ∑ b : Fin d,
            (siteOp i (gen d a b) ⊗ₖ (1 : Matrix (Fin nB → Fin d) (Fin nB → Fin d) ℂ)) *
              ((1 : Matrix (Fin nA → Fin d) (Fin nA → Fin d) ℂ) ⊗ₖ siteOp j (gen d b a)) +
          ((d : ℂ)⁻¹) • (1 : Matrix (Cfg d nA nB) (Cfg d nA nB) ℂ) := by sorry

end WernerExt.TwoSided
