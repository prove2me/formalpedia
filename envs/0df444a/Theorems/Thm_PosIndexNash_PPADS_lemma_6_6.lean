-- Prove2me | Theorems.Thm_PosIndexNash_PPADS_lemma_6_6
-- name    : PosIndexNash.PPADS.lemma_6_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:33:25.681463+00:00
-- url     : https://prove2.me/theorems/9672c617-c3ce-4913-9dbb-215442713749
-- title:
--   Lemma 6.6 — effective perturbation: for ε = 2^{−κ}, G(ε) is globally nondegenerate and its equilibria match those of G(0) with supports and index
-- statement:
--   In the setting of §6, let $c > 1 + \max_{i,j}|S_{ij}|$ be an integer, $R = S + c\mathbf 1\mathbf 1^\top$, $C = I_N$, $R(t) = D(t)^{-1}R$ and $G(t) = (R(t), C)$, and let $L_{\mathrm{enc}}$ be the binary encoding length of $(R, C)$. One can compute, in time polynomial in $N + L_{\mathrm{enc}}$, an integer $\kappa = \mathrm{poly}(N, L_{\mathrm{enc}})$ such that for $\varepsilon = 2^{-\kappa}$:
--
--   1. the rational game $G(\varepsilon)$ is globally nondegenerate and has encoding length polynomial in $N + L_{\mathrm{enc}}$;
--   2. there is a one-to-one correspondence between the equilibria of $G(0)$ and those of $G(\varepsilon)$; corresponding equilibria have the same row support, the same column support and the same index;
--   3. in particular, $G(\varepsilon)$ has no additional equilibria.
--
--   In Lean: there are a function $\kappa$ of the code of $(R, C)$, computable (in binary) in polynomial time, and polynomials $p_\kappa, p_{\mathrm{enc}}$, fixed before the instance, with $\kappa \le p_\kappa(N + L_{\mathrm{enc}})$, $|\mathrm{code}(G(\varepsilon))| \le p_{\mathrm{enc}}(N + L_{\mathrm{enc}})$, $G(\varepsilon)$ nondegenerate, and a bijection $e$ from the equilibria of $G(0)$ onto those of $G(\varepsilon)$ preserving both supports and the Shapley index:
--   $$\mathrm{supp}\, e(p,q)_1 = \mathrm{supp}\, p,\quad \mathrm{supp}\, e(p,q)_2 = \mathrm{supp}\, q,\quad \mathrm{ind}_{G(\varepsilon)}(e(p,q)) = \mathrm{ind}_{G(0)}(p,q).$$
--
--   Differences from the source:
--   - generalization: "the game built from the LCP (42) of §5" → the game built from any anchored normal form whose LCP solutions are strictly complementary and regular, for every integer $c > 1 + \max|S_{ij}|$; reason: the proof uses only these properties (through Lemmas 6.3 and 6.5); the paper's game is one such, so the statement specializes.
--   - encoding: "compute in time polynomial in $N + L_{\mathrm{enc}}$ an integer $\kappa = \mathrm{poly}(N, L_{\mathrm{enc}})$", "encoding length polynomial" → a map from the code `RatGame.enc` of $(R, I_N)$ to `encBin κ` computable in polynomial time on Cook's Turing machines, and explicit polynomials $p_\kappa, p_{\mathrm{enc}} \in \mathbb{N}[X]$ chosen before all instances, evaluated at $N + L_{\mathrm{enc}}$ with $L_{\mathrm{enc}} = |\mathrm{enc}(R, I_N)|$; reason: the meaning of "polynomial", uniform in the instance.
--   - encoding: $\alpha_i(t) = 1 + t^i$, $i\in[N]$; "no additional equilibria" → $1 + t^{i+1}$ for the 0-based strategy $i$; part 3 is the surjectivity of the bijection $e$; reason: Lean indexing; part 3 is stated as a consequence of part 2.
-- source:
--   Kontogiannis, Panageas, Pollatos, Yan, Finding a Positive Index Nash Equilibrium is PPADS-Complete, arXiv:2609.23879 (held PDF, sha256 00d5c5ce…cbb6), p. 45, Lemma 6.6

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding
import Definitions.Def_QuasiStrictNE_supp
import Definitions.Def_QuasiStrictNE_IsNE
import Definitions.Def_QuasiStrictNE_RatGame
import Definitions.Def_QuasiStrictNE_RatGame_enc
import Definitions.Def_PosIndexNash_PPADS_NormalForm
import Definitions.Def_PosIndexNash_PPADS_LCP
import Definitions.Def_PosIndexNash_PPADS_ImitationGame
import Definitions.Def_PosIndexNash_PPADS_Nondegenerate
import Definitions.Def_PosIndexNash_PPADS_ShapleyIndex

open Matrix QAlgorithms.LocalHamiltonian

namespace PosIndexNash.PPADS

theorem lemma_6_6 :
    ∃ (kappa : List Bool → ℕ) (pk pe : Polynomial ℕ),
      CookPvsNP.PolyTimeComputable (fun s => encBin (kappa s)) ∧
      ∀ (F : NormalForm) (hF : F.Anchored)
    (hsc : ∀ x ∈ LCPSol (F.M.map ((↑) : ℚ → ℝ)) (-(fun i => (F.b i : ℝ))),
      ∀ i, 0 < x i + ((F.M.map ((↑) : ℚ → ℝ)) *ᵥ x - fun i => (F.b i : ℝ)) i)
    (hreg : ∀ x ∈ LCPSol (F.M.map ((↑) : ℚ → ℝ)) (-(fun i => (F.b i : ℝ))),
      ((F.M.map ((↑) : ℚ → ℝ)).submatrix
        (Subtype.val : {i // i ∈ QuasiStrictNE.supp x} → Fin F.m) Subtype.val).det ≠ 0)
        (c : ℤ), (∀ i j, 1 + |symGameS F i j| < (c : ℚ)) →
        kappa (perturbedGame F c 0).enc ≤ pk.eval (F.m + 1 + (perturbedGame F c 0).enc.length) ∧
        Nondegenerate
          ((perturbedR F c (2 ^ kappa (perturbedGame F c 0).enc)⁻¹).map ((↑) : ℚ → ℝ))
          (1 : Matrix (Fin (F.m + 1)) (Fin (F.m + 1)) ℝ) ∧
        (perturbedGame F c (2 ^ kappa (perturbedGame F c 0).enc)⁻¹).enc.length ≤
          pe.eval (F.m + 1 + (perturbedGame F c 0).enc.length) ∧
        ∃ e : {p : (Fin (F.m + 1) → ℝ) × (Fin (F.m + 1) → ℝ) //
              QuasiStrictNE.IsNE ((perturbedR F c 0).map ((↑) : ℚ → ℝ))
                (1 : Matrix (Fin (F.m + 1)) (Fin (F.m + 1)) ℝ) p.1 p.2} ≃
            {p : (Fin (F.m + 1) → ℝ) × (Fin (F.m + 1) → ℝ) //
              QuasiStrictNE.IsNE
                ((perturbedR F c (2 ^ kappa (perturbedGame F c 0).enc)⁻¹).map ((↑) : ℚ → ℝ))
                (1 : Matrix (Fin (F.m + 1)) (Fin (F.m + 1)) ℝ) p.1 p.2},
          ∀ p, QuasiStrictNE.supp (e p).1.1 = QuasiStrictNE.supp p.1.1 ∧
            QuasiStrictNE.supp (e p).1.2 = QuasiStrictNE.supp p.1.2 ∧
            shapleyIndex
                ((perturbedR F c (2 ^ kappa (perturbedGame F c 0).enc)⁻¹).map ((↑) : ℚ → ℝ))
                (1 : Matrix (Fin (F.m + 1)) (Fin (F.m + 1)) ℝ) (e p).1.1 (e p).1.2 =
              shapleyIndex ((perturbedR F c 0).map ((↑) : ℚ → ℝ))
                (1 : Matrix (Fin (F.m + 1)) (Fin (F.m + 1)) ℝ) p.1.1 p.1.2 := by sorry

end PosIndexNash.PPADS
