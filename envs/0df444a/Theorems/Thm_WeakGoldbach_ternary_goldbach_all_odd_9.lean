-- Prove2me | Theorems.Thm_WeakGoldbach_ternary_goldbach_all_odd_9
-- name    : WeakGoldbach.ternary_goldbach_all_odd_9
-- status  : Open
-- author  : @WillR
-- created : 2026-10-01T11:02:13.692342+00:00
-- url     : https://prove2.me/theorems/e987963c-168d-4ccd-9817-d1431ee225c4
-- title:
--   Helfgott ternary Goldbach for every odd integer at least $9$
-- statement:
--   Every odd natural number $n \ge 9$ is a sum of three **odd** primes:
--
--   $$\exists\; p, q, r \text{ odd primes with } n = p + q + r.$$
--
--   This is Helfgott's ternary Goldbach theorem (arXiv:1312.7748, Theorem 1) with the correct lower bound. The floor matters: the sum of three odd primes is odd, and the smallest such sum is $3 + 3 + 3 = 9$, so $9 \le n$ is the exact threshold. The value $n = 7$ is odd and admits no such decomposition, which is why the previously published record `WeakGoldbach.ternary_goldbach_all_odd`, stating the theorem with the weaker floor $5 < n$, is false and is marked Disproved.
--
--   This statement is the corrected form and is the node from which the effective circle-method regime $10^{27} \le n < e^{3100}$ (Helfgott) and the effective-Vinogradov regime $n \ge e^{3100}$ (Liu--Wang) should be derived.
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, arXiv:1312.7748, Theorem 1, https://arxiv.org/abs/1312.7748. Corrects the floor of the Disproved record WeakGoldbach.ternary_goldbach_all_odd (4e160e92-64f7-4655-94d2-59765f804d0c) from `5 < n` to `9 <= n`; the published floor is refuted by n = 7.

import Mathlib

namespace WeakGoldbach

theorem ternary_goldbach_all_odd_9 (n : Nat) (hlo : 9 <= n) (hodd : Odd n) :
    Exists fun p : Nat => Exists fun q : Nat => Exists fun r : Nat =>
      And (Nat.Prime p) (And (Nat.Prime q) (And (Nat.Prime r)
        (And (Odd p) (And (Odd q) (And (Odd r) (n = p + q + r)))))) := by sorry

end WeakGoldbach
