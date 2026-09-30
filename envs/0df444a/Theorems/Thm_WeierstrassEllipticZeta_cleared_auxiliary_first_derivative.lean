-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_cleared_auxiliary_first_derivative
-- name    : WeierstrassEllipticZeta.cleared_auxiliary_first_derivative
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-08T00:12:44.037552+00:00
-- url     : https://prove2.me/theorems/ecd3aa52-3e08-4e87-b1ce-693193154e89
-- title:
--   Exact first derivative of the cleared auxiliary translate
-- statement:
--   Let $L$ be a complex period pair with lattice $\Lambda$ and canonical Weierstrass functions $\wp,\zeta$. Assume $\zeta'(w)=-\wp(w)$ outside $\Lambda$. Let $I$ be any finite index set, choose complex coefficients $c_i$, nonnegative integer exponents $d_i,b_i,e_i$, a nonnegative integer $M$, and a shift $v\notin\Lambda$. Define
--
--   $$F(w)=\sum_{i\in I}c_i w^{d_i}\wp(w)^{b_i}\zeta(w)^{e_i},$$
--
--   $$H_v(z)=\sum_{i\in I}c_i(z+v)^{d_i}[2(\wp(v)-\wp(z))]^{3M}\wp(z+v)^{b_i}\zeta(z+v)^{e_i}.$$
--
--   At every point $z$ with $z,z+v\notin\Lambda$, the function $H_v$ is analytic. For every nonnegative integer $n$ such that
--
--   $$F^{(j)}(z+v)=0\qquad(0\le j<n),$$
--
--   one has the exact identity
--
--   $$H_v^{(n)}(z)=[2(\wp(v)-\wp(z))]^{3M}F^{(n)}(z+v).$$
--
--   No nonzero derivative is asserted. The clearing factor may vanish, and no regularity assumption on $z-v$ is needed. Order zero, $M=0$, zero coefficients and the empty finite sum are included. The exponents need no bounds relative to $M$, because this is a local derivative identity rather than an assertion of entire regularization. This identity transfers lower-derivative vanishing and identifies the first potentially nonzero derivative of the cleared translate.
-- source:
--   Senthil Kumar K (2026), Lemma 6(ii) and Section 5 equations (34)–(35), https://doi.org/10.1017/S001309152610145X. The exact multiplier identity follows from the translated derivative identity and Leibniz formula when every lower derivative vanishes; this statement isolates that local analytic step without requiring the derivative or multiplier to be nonzero.

import Definitions.Def_WeierstrassEllipticZeta_ClearedEntire
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.cleared_auxiliary_first_derivative
    (L : PeriodPair)
    (h_zeta_deriv : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    {ι : Type} [Fintype ι] (v : ℂ) (_hv : v ∉ L.lattice)
    (c : ι → ℂ) (l₀ l₂ l₃ : ι → ℕ) (M : ℕ)
    (z : ℂ) (hz : z ∉ L.lattice) (hp : z + v ∉ L.lattice) :
    AnalyticAt ℂ (clearedAuxiliarySum L v c l₀ l₂ l₃ M) z ∧
      ∀ n : ℕ,
        (∀ j < n, iteratedDeriv j (fun w => ∑ i, c i * w ^ l₀ i *
          L.weierstrassP w ^ l₂ i * weierstrassZeta L w ^ l₃ i) (z + v) = 0) →
        iteratedDeriv n (clearedAuxiliarySum L v c l₀ l₂ l₃ M) z =
          (2 * (L.weierstrassP v - L.weierstrassP z)) ^ (3 * M) *
            iteratedDeriv n (fun w => ∑ i, c i * w ^ l₀ i *
              L.weierstrassP w ^ l₂ i * weierstrassZeta L w ^ l₃ i) (z + v) := by sorry
