-- Prove2me | Theorems.Thm_RobustCorrClust_Main_lemma_5_21
-- name    : RobustCorrClust.Main.lemma_5_21
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:41:30.74455+00:00
-- url     : https://prove2.me/theorems/10ea6b9f-f0f8-42ab-83bf-df67c855635d
-- title:
--   Lemma 5.21 — Chebyshev approximation of the positive part: |p_{ρ,N}(M)_uv − (M⁺)_uv| ≤ ρ/(π(2N+1)) ≤ ρ/(2N)
-- statement:
--   Let $\rho>0$, $N\ge1$ and $\alpha_N:=\rho/(\pi(2N+1))$. For every real symmetric $n\times n$ matrix $M$ with $\|M\|_{\mathrm{op}}\le\rho$ (spectral norm),
--   $$\big|(p_{\rho,N}(M))_{uv}-(M^+)_{uv}\big|\le\alpha_N\le\frac{\rho}{2N}\qquad\text{for all vertices }u,v,$$
--   where $p_{\rho,N}(t)=\rho\sum_{k=0}^{2N}c_kT_k(t/\rho)$ (Definition 9) is applied as a matrix polynomial. A column of $M^+$ can therefore be approximated using only products with $M$.
--
--   Differences from the source:
--   - reading: $p_{R,N}$ → $p_{\rho,N}$; reason: subscript slip, Definition 9 defines the polynomial with parameter $\rho$.
--   - encoding: $\|M\|_{\mathrm{op}}\le\rho$ → $\|Mx\|_2^2\le\rho^2\|x\|_2^2$ for every $x$; reason: the spectral norm, written with squared Euclidean norms.
-- source:
--   Cao, Fabius, Wang, Efficient Correlation Clustering in Single-pass Graph Streams: Deterministic and Adversarially Robust, STOC 2027 submission (sha256 814ae686…), p. 41, Lemma 5.21

import Mathlib
import Definitions.Def_RobustCorrClust_Main_NCMDual
import Definitions.Def_RobustCorrClust_Main_Chebyshev

namespace RobustCorrClust.Main

/-- Lemma 5.21 (p. 41): let `ρ > 0`, `N ≥ 1` and `α_N := ρ/(π(2N+1))`. For every symmetric `M`
with `‖M‖_op ≤ ρ`, `|(p_{ρ,N}(M))_uv − (M⁺)_uv| ≤ α_N ≤ ρ/(2N)` for all vertices `u, v`. -/
theorem lemma_5_21 (ρ : ℝ) (hρ : 0 < ρ) (N : ℕ) (hN : 1 ≤ N) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) (hop : OpNormLE M ρ) :
    (∀ u v, |Polynomial.aeval M (chebPoly ρ N) u v - posPart M u v| ≤
        ρ / (Real.pi * (2 * N + 1))) ∧
    ρ / (Real.pi * (2 * N + 1)) ≤ ρ / (2 * N) := by sorry

end RobustCorrClust.Main
