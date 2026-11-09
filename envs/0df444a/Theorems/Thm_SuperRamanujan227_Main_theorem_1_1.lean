-- Prove2me | Theorems.Thm_SuperRamanujan227_Main_theorem_1_1
-- name    : SuperRamanujan227.Main.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:40:49.898416+00:00
-- url     : https://prove2.me/theorems/1fcae90a-1c38-4991-97e1-9a4d1a6d6a2b
-- title:
--   Theorem 1.1 — $d$-regular graphs with $\lambda_2\le2\sqrt{d-1}-\frac{3}{4^{1/3}}(1-\frac2d)^{5/3}\sqrt d/n^{2/3}$
-- statement:
--   For every even integer $n\ge2$ and every integer $d\ge3$ there exists a $d$-regular graph $G$ on $n$ vertices (parallel edges and self-loops allowed, a self-loop counting $2$ towards the degree) such that
--   $$\lambda_2(G)\le2\sqrt{d-1}-\frac{3}{4^{1/3}}\Big(1-\frac2d\Big)^{5/3}\frac{\sqrt d}{n^{2/3}}\le2\sqrt{d-1}-\frac{\sqrt d}{4n^{2/3}}.$$
--   Here $\lambda_2(G)$ is the second largest adjacency eigenvalue counted with multiplicity. There is no upper bound on $d$ in terms of $n$.
--
--   Thus for every even $n$ and every $d\ge3$ there is a one-sided super-Ramanujan graph whose second eigenvalue lies below the Ramanujan threshold $2\sqrt{d-1}$ by an explicit, nonasymptotic margin of order $\sqrt d/n^{2/3}$.
--
--   **Formalization Note** All powers are real powers of positive reals; $n,d$ are cast to $\mathbb R$ before subtraction and division. The second inequality is stated as a separate conjunct.
--
--   Differences from the source:
--   - encoding: a d-regular graph G on n vertices (parallel edges and self-loops allowed, §2) → a symmetric ℕ-valued adjacency matrix on Fin n with even diagonal and all row sums d; reason: §2's adjacency convention; these matrices are exactly the adjacency matrices of such multigraphs
--   - encoding: λ_2(G), second eigenvalue in d = λ_1 ≥ λ_2 ≥ ⋯ ≥ λ_n → second largest real root, with multiplicity, of the characteristic polynomial of the real adjacency matrix; reason: the adjacency matrix is real symmetric, so its characteristic polynomial has n real roots, its eigenvalues
-- source:
--   Gil Cohen, Gal Maor, Quantitative Results on Super-Ramanujan Graphs, STOC 2027 submission #227 (October 2026), SHA-256 1ba5eacb267c8a63eff5e5b9d6b96d9f2b04d5a1e147d887b9e61574127831f8, Theorem 1.1, p. 4

import Mathlib
import Definitions.Def_SuperRamanujan227_Main_Spectra
import Definitions.Def_SuperRamanujan227_Main_Multigraph
open Polynomial

namespace SuperRamanujan227.Main

/-- Theorem 1.1 (p. 4): for every even `n ≥ 2` and integer `d ≥ 3` there is a `d`-regular
multigraph `G` on `n` vertices (parallel edges and self-loops allowed, a loop counting twice) with
`λ₂(G) ≤ 2√(d-1) - (3/4^{1/3})(1 - 2/d)^{5/3} √d / n^{2/3} ≤ 2√(d-1) - √d / (4 n^{2/3})`. -/
theorem theorem_1_1 (n d : ℕ) (hn : Even n) (hn2 : 2 ≤ n) (hd : 3 ≤ d) :
    ∃ G : Multigraph n, G.IsRegular d ∧
      G.eig 2 ≤ 2 * Real.sqrt ((d : ℝ) - 1) -
          3 / (4 : ℝ) ^ ((1 : ℝ) / 3) * (1 - 2 / (d : ℝ)) ^ ((5 : ℝ) / 3) * Real.sqrt (d : ℝ) /
            (n : ℝ) ^ ((2 : ℝ) / 3) ∧
      2 * Real.sqrt ((d : ℝ) - 1) -
          3 / (4 : ℝ) ^ ((1 : ℝ) / 3) * (1 - 2 / (d : ℝ)) ^ ((5 : ℝ) / 3) * Real.sqrt (d : ℝ) /
            (n : ℝ) ^ ((2 : ℝ) / 3) ≤
        2 * Real.sqrt ((d : ℝ) - 1) - Real.sqrt (d : ℝ) / (4 * (n : ℝ) ^ ((2 : ℝ) / 3)) := by sorry

end SuperRamanujan227.Main
