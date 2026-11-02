-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P76_conditional_sum_identity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P76.conditional_sum_identity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:20:25.54057+00:00
-- url     : https://prove2.me/theorems/60beed75-be0e-4759-9c99-7761b5ff14d9
-- title:
--   Lemma 6: conditional Ahlswede–Csiszar sum identity (attributed prior result)
-- statement:
--   Let $K,\Phi,Y^n,Z^n$ be arbitrary finite random variables on one normalized finite probability space. All information is in bits. Then
--   $$I(K;Y^n\mid\Phi)-I(K;Z^n\mid\Phi)=\sum_{i=1}^n\bigl[I(K;Y_i\mid Y^{i-1},Z_{i+1}^n,\Phi)-I(K;Z_i\mid Y^{i-1},Z_{i+1}^n,\Phi)\bigr].$$
--   The case $n=0$ has empty sum and zero on both sides. The Lean masks store exactly the prefix before $i$ and suffix after $i$, with fixed `none` entries elsewhere.
-- source:
--   The Sender-Excited Secret Key Agreement Model: Capacity, Reliability and Secrecy Exponents, arXiv:1107.4148v4, PDF p. 11, Lemma 6, explicitly citing [3, Lemma 4.1]

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P76

namespace QAlgorithms.Papers.Independent.Intakethird100.P76

noncomputable section

open scoped BigOperators

open Filter Set

attribute [local instance] Classical.propDecidable

-- Exact pinned primitives, inspected at their definitions before reuse.

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

variable {S X Y Z : Type} [Fintype S] [Fintype X] [Fintype Y] [Fintype Z]
  [Nonempty S] [Nonempty X] [Nonempty Y] [Nonempty Z]

variable {n u w : ℕ}

/-- PDF p.11, Lemma 6, explicitly attributed there to Ahlswede--Csiszar
[3, Lemma 4.1]. Arbitrary finite random variables on one normalized sample law.
The Option masks encode exactly Y before i and Z after i; all other entries
are fixed None and carry no information. For n=0 both sides are zero. -/
theorem conditional_sum_identity {O K P A B : Type*}
    [Fintype O] [Fintype K] [Fintype P] [Fintype A] [Fintype B]
    (p : O → ℝ) (hp : IsLaw p) (k : O → K) (phi : O → P)
    (n : ℕ) (y : O → Fin n → A) (z : O → Fin n → B) :
    condInfo p k y phi - condInfo p k z phi =
      ∑ i : Fin n,
        (condInfo p k (fun o => y o i)
          (fun o => ((fun j : Fin n => if j < i then some (y o j) else none),
            (fun j : Fin n => if i < j then some (z o j) else none), phi o)) -
        condInfo p k (fun o => z o i)
          (fun o => ((fun j : Fin n => if j < i then some (y o j) else none),
            (fun j : Fin n => if i < j then some (z o j) else none), phi o))) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P76
