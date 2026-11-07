-- Prove2me | Theorems.Thm_PNormReg_lemma_19
-- name    : PNormReg.lemma_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:41:23.199757+00:00
-- url     : https://prove2.me/theorems/3b34cef6-c9a5-40d7-95fa-d71d7c2fc1b7
-- title:
--   Lemma 19, p.37 — $(Z,\|\cdot\|_\cdot,r,\Xi,\mathrm{clip})$ of (49)–(51) is a local-norm setup
-- statement:
--   Let $q\in(1,2]$, $p=q/(q-1)$, $d,n\ge1$, and $\tau_i>0$. On $Z=B^d_2\times B^n_q$ define
--
--   $$r(x,y)=\tfrac12\|x\|_2^2+\frac{\|y\|_q^q}{q(q-1)},\qquad\Xi=\tfrac12+\frac1{q(q-1)},$$
--
--   $$\|(u,v)\|^2_{(x,y)}=\|u\|_2^2+\sum_{i=1}^n\Big(\tau_i^{p-2}+\frac{|y_i|}{\tau_i}\Big)v_i^2,$$
--
--   $$\mathrm{clip}(u,v)=\big(u,(\mathrm{sign}(v_i)\min\{|v_i|,\tau_i\})_{i=1}^n\big).$$
--
--   Then $(Z,\|\cdot\|_\cdot,r,\Xi,\mathrm{clip})$ is a local-norm setup in the sense of Definition 5.
--
--   The added baseline $\tau_i^{p-2}$ and the term $|y_i|/\tau_i$ are what make the local norm work at $y_i=0$, where the inverse Hessian of the regularizer fails.
--
--   Differences from the source:
--   - generalization: τ_i as defined in Algorithm 6 → every τ with τ_i > 0; reason: p.38: "Lemma 19 in fact holds for any τ_i > 0"; Algorithm 6's thresholds are positive under (40)
--   - encoding: d and n left implicit → 1 ≤ d, 1 ≤ n; reason: with an empty factor the range of r differs from the printed Ξ; M ∈ ℝ^{n×d} with rows and columns is what the section treats
-- source:
--   Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission (manuscript sha256 e335b2fa…), Lemma 19, p.37 (PDF p.38); Definition 5, p.36; remark, p.38

import Mathlib
import Definitions.Def_PNormReg_SMD

namespace PNormReg

/-- **Lemma 19** with Definition 5, p.37 (PDF p.38); (49)–(51).

Adil, Bullins, O'Carroll, Sidford, *Solving p-norm regression in matrix multiplication time*, STOC 2027
submission (manuscript sha256 e335b2fa…).

For `q ∈ (1, 2]` and every `τ > 0`, the data of (49)–(51) on `Z = B^d_2 × B^n_q` is a local-norm setup.

**Formalization Note.** p.38: "Lemma 19 in fact holds for any τ_i > 0", so the thresholds are free; the
ones of Algorithm 6 are positive by the standing assumption of (40). `d, n ≥ 1` because with an empty
factor the range of `r` differs from the printed `Ξ`. -/
theorem lemma_19 {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (q : ℝ) (hq₁ : 1 < q) (hq₂ : q ≤ 2)
    (τ : Fin n → ℝ) (hτ : ∀ i, 0 < τ i) :
    LocalNormData.IsLocalNormSetup (l2lqSetup q τ : LocalNormData d n) := by sorry

end PNormReg
