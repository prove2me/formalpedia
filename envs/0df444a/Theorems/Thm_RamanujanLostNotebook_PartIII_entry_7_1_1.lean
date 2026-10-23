-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartIII_entry_7_1_1
-- name    : RamanujanLostNotebook.PartIII.entry_7_1_1
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-08T21:32:42.397834+00:00
-- url     : https://prove2.me/theorems/6e9e2a1f-8e97-4ca8-a4ee-58ba2f830fde
-- title:
--   τ₂(n) ≡ σ₁₅(n) (mod 3617) for the coefficients τ₂ of QΔ
-- statement:
--   Let $\sigma_k(n)=\sum_{d\mid n}d^k$ (sum over the positive divisors of $n$) and $\Delta=q\prod_{j\ge1}(1-q^j)^{24}$, let $Q=1+240\sum_{m\ge1}\sigma_3(m)q^m$ (Ramanujan's Eisenstein series $E_4$), and define the integers $\tau_2(n)$ by $\sum_{n\ge1}\tau_2(n)q^n=Q\Delta$ (formal power series in $q$). Then for every integer $n\ge1$, $\tau_2(n)-\sigma_{15}(n)\equiv0\pmod{3617}$.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 7, Entry 7.1.1, p. 206, eq. (7.1.5).

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIII_ch07_deltaTrunc
import Definitions.Def_RamanujanLostNotebook_PartIII_ch07_divisorSigma
import Definitions.Def_RamanujanLostNotebook_PartIII_ch07_eisensteinQTrunc
import Definitions.Def_RamanujanLostNotebook_PartIII_ch07_tau2

namespace RamanujanLostNotebook.PartIII
theorem entry_7_1_1 (n : ℕ) (hn : 0 < n) :
    (3617 : ℤ) ∣ tau2 n - divisorSigma 15 n := by sorry
end RamanujanLostNotebook.PartIII
