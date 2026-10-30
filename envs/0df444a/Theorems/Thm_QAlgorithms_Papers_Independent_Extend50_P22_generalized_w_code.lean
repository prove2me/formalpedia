-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P22_generalized_w_code
-- name    : QAlgorithms.Papers.Independent.Extend50.P22.generalized_w_code
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:31:03.237741+00:00
-- url     : https://prove2.me/theorems/ef42d01d-4560-4416-92a3-a375b8e4f4be
-- title:
--   Unnumbered generalized W-state covariant code, Eqs.(55)–(58)
-- statement:
--   Let an isometry $V:L\to\bigotimes_{i=1}^n A_i$ encode a logical system of dimension $d\ge1$ into $n\ge1$ finite subsystems of positive dimensions $d_i$. A located erasure replaces erased sites by fixed pure states and supplies an orthogonal location flag. Write $\epsilon_{\rm worst}=\sqrt{1-f_{\rm worst}^2}$, where one CPTP recovery is optimized before minimizing root entanglement fidelity over all unit vectors on $L\otimes R$, with $R\simeq L$. Write $\epsilon_e=\sqrt{1-f_e^2}$ for optimal root entanglement fidelity at the normalized maximally entangled input. Unless specified otherwise, single-site erasure is uniform. For each $d,n\ge1$, give every physical site one extra orthogonal basis vector $|\perp\rangle$. The fixed normalized encoding is $$|\psi\rangle\longmapsto\frac1{\sqrt n}\sum_{i=1}^n|\perp,\ldots,\psi_i,\ldots,\perp\rangle.$$ It is isometric and covariant under the full logical $U(d)$ group by the local action $U\oplus1$, with $$\epsilon_{\rm worst}\le\frac{\sqrt2+d}{\sqrt n}.$$ The error is worst-case over entangled inputs, not an average over logical states.
-- source:
--   Continuous symmetries and approximate quantum error correction, arXiv:1902.07714v1, PDF p. 16, Unnumbered generalized W-state covariant code, Eqs.(55)–(58)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Support21.P09 (Irreducible)

open QAlgorithms.Papers.Independent.Renew46.P45 (symmetricWeight)

/-- PDF p.16, (55)–(58): the actual W isometry, full unitary covariance, and worst-case
bound (sqrt(2)+d)/sqrt(n). The code witness supplies the isometry proof for this fixed matrix. -/
theorem generalized_w_code (d n : ℕ) (hd : 0 < d) (hn : 0 < n) :
    ∃ c : CovariantErasureCodeData d n, c.dims = (fun _ => d + 1) ∧ HEq c.V (wEncoding d n) ∧
      Nonempty (FullAction c) ∧
      errorWorst c.uniformNoise ≤ (Real.sqrt 2 + d) / Real.sqrt n := by sorry

end QAlgorithms.Papers.Independent.Extend50.P22

end
