-- Prove2me | Theorems.Thm_PriceCapacities_LowerBound_proposition_B_3
-- name    : PriceCapacities.LowerBound.proposition_B_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:22:22.930552+00:00
-- url     : https://prove2.me/theorems/6e86047a-abd2-44b2-9c24-af987bce3dc1
-- title:
--   Proposition B.3 — even parity vectors diagonalize $M_{ab}=g(y_a\odot y_b)$; $s_{\min}(M)=N\min_{|S|\text{ even}}|\hat g(S)|$
-- statement:
--   Let $d\ge1$ and $g:\{-1,1\}^d\to\mathbb R$ with $g(-y)=g(y)$. Let $N=2^{d-1}$ and choose $y_1,\dots,y_N$ containing exactly one vector from each opposite pair $\{y,-y\}$. Let $M$ be the $N\times N$ matrix with entries
--   $$M_{ab}=g(y_a\odot y_b)\qquad(a,b\in[N]).$$
--   For each $S\subseteq[d]$ with $|S|$ even let $\chi_S\in\mathbb R^N$ have coordinates $\chi_S(a)=\chi_S(y_a)$. Then these $N$ vectors form an orthogonal basis of $\mathbb R^N$ (distinct even $S,T$ give orthogonal vectors, each vector is nonzero, and together they span $\mathbb R^N$), and
--   $$M\chi_S=N\,\hat g(S)\,\chi_S .$$
--   Consequently the least singular value of $M$ is
--   $$s_{\min}(M)=N\min_{S\subseteq[d],\ |S|\text{ even}}|\hat g(S)| .$$
--   In Lemma 10.6 this turns the Fourier coefficients of $y\mapsto|\sum_jy_j|$ into a lower bound on the eigenvalues of the matrix $(|\langle\theta,x\rangle|/N)_{\theta,x\in G}$.
--
--   Differences from the source:
--
--   - encoding: y_1, …, y_N containing exactly one vector from each opposite pair, N = 2^{d−1} → y : Fin (2^(d−1)) → Cube d with ∀ v, ∃! a, y a = v ∨ y a = −v (0-based); reason: same condition
--   - encoding: d unrestricted (N = 2^{d−1}) → hypothesis 1 ≤ d; reason: N = 2^{d−1} is not an integer at d = 0; the hypothesis excludes only that undefined case
--   - encoding: the N vectors form an orthogonal basis → pairwise orthogonal for distinct even S, T, each nonzero, and spanning ℝ^N; reason: orthogonal nonzero spanning vectors form an orthogonal basis
--   - encoding: s_min(M) and min over even S → leastSingularValue M = inf of ‖Mv‖₂ over unit v; ⨅ over the finite nonempty type of even subsets; reason: for a square matrix s_min is the minimum of ‖Mv‖₂ on the unit sphere; both infima are attained minima
-- source:
--   Prabhu, Schwiegelshohn, Shyam, The Price of Capacities for Clustering Coresets, STOC 2027 submission (manuscript sha256 ec35f5ef…), p. 62, Proposition B.3

import Mathlib
import Definitions.Def_PriceCapacities_LowerBound_Fourier

namespace PriceCapacities.LowerBound

theorem proposition_B_3 (d : ℕ) (hd : 1 ≤ d) (g : Cube d → ℝ) (hg : ∀ y, g (-y) = g y)
    (y : Fin (2 ^ (d - 1)) → Cube d) (hy : ∀ v : Cube d, ∃! a, y a = v ∨ y a = -v) :
    (∀ S T : Finset (Fin d), Even S.card → Even T.card → S ≠ T →
      ∑ a, parity S (y a) * parity T (y a) = 0) ∧
    (∀ S : Finset (Fin d), Even S.card → (fun a => parity S (y a)) ≠ 0) ∧
    Submodule.span ℝ {v : Fin (2 ^ (d - 1)) → ℝ |
      ∃ S : Finset (Fin d), Even S.card ∧ v = fun a => parity S (y a)} = ⊤ ∧
    (∀ S : Finset (Fin d), Even S.card →
      (Matrix.of fun a b => g (y a * y b)).mulVec (fun a => parity S (y a))
        = (((2 ^ (d - 1) : ℕ) : ℝ) * fourierCoeff g S) • (fun a => parity S (y a))) ∧
    leastSingularValue (Matrix.of fun a b => g (y a * y b))
      = ((2 ^ (d - 1) : ℕ) : ℝ) *
          ⨅ S : {S : Finset (Fin d) // Even S.card}, |fourierCoeff g S.1| := by sorry

end PriceCapacities.LowerBound
