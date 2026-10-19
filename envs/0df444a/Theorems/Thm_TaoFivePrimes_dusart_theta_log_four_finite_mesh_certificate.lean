-- Prove2me | Theorems.Thm_TaoFivePrimes_dusart_theta_log_four_finite_mesh_certificate
-- name    : TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-14T12:59:31.605976+00:00
-- url     : https://prove2.me/theorems/ac40c234-e6c8-4c90-86d2-abb6b1f5f51a
-- title:
--   Finite theta certificate on a sixteenth-integer mesh through exp(23)
-- statement:
--   For each integer $32\le n\le\lceil16e^{23}\rceil$, put $a=n/16$ and $b=(n+1)/16$. The finite certificate requires both endpoint inequalities
--
--   $$|\vartheta(a)-a|\le\frac{151.3a}{\log^4 b},\qquad |\vartheta(a)-b|\le\frac{151.3a}{\log^4 b}.$$
--
--   The Chebyshev theta function is constant between successive points of this mesh, since every integer lies on the mesh. These finite endpoint inequalities imply the desired estimate for all real $2\le x\le e^{23}$. This is a sufficient strengthened checkpoint form of the direct finite inspection in Dusart's proof; it is a derived auxiliary certificate, not a verbatim statement from the paper.
-- source:
--   Derived finite checkpoint formulation for the direct inspection in P. Dusart, Ramanujan J.45 (2018), Theorem 4.2 and its proof, printed p.237. The paper locates the weighted theta-error maximum immediately below 1423, approximately 151.2235681. https://piyanit.nl/wp-content/uploads/2020/10/art_10.1007_s11139-016-9839-4.pdf.

import Mathlib.NumberTheory.Chebyshev

theorem TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate
    (n : ℕ) (hn : 32 ≤ n) (hcap : n ≤ Nat.ceil (16 * Real.exp 23)) :
    let a : ℝ := (n : ℝ) / 16
    let b : ℝ := ((n : ℝ) + 1) / 16
    |Chebyshev.theta a - a| ≤ (1513 / 10 : ℝ) * a / (Real.log b)^4 ∧
      |Chebyshev.theta a - b| ≤ (1513 / 10 : ℝ) * a / (Real.log b)^4 := by sorry
