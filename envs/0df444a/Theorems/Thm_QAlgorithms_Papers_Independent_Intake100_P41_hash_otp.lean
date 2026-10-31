-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P41_hash_otp
-- name    : QAlgorithms.Papers.Independent.Intake100.P41.hash_otp
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:22:11.718371+00:00
-- url     : https://prove2.me/theorems/ebf6a8f5-6aaa-4092-a98d-977e80c3c020
-- title:
--   Three hash-and-OTP consequences of AXU2 hashing
-- statement:
--   Let $K$ be finite and nonempty, let $X$ be any message alphabet, and let $T=\{0,1\}^m$ for $m\ge0$. Let $h:K\times X\to T$ be $\varepsilon$-AXU$_2$, with $\varepsilon\ge0$. For independent uniform $k\in K$ and $p\in T$, set $g_{k,p}(x)=h_k(x)\oplus p$. Then:
--
--   1. For $x\ne y$ and $a,b\in T$,
--   $$
--   \Pr[g_{k,p}(x)=a,\ g_{k,p}(y)=b]\le\frac{\varepsilon}{|T|}.
--   $$
--   2. For each fixed $k\in K$, message $x$, and tag $a$,
--   $$
--   \Pr_p[g_{k,p}(x)=a]=\frac1{|T|}.
--   $$
--   3. For $x\ne y$ and $a,b\in T$,
--   $$
--   \Pr[g_{k,p}(y)=b\mid g_{k,p}(x)=a]\le\varepsilon.
--   $$
--
--   Thus OTP padding gives the source's ASU$_2$ pair bound, tag uniformity independent of the hash index, and the conditional forgery bound. The conditioning probability is $1/|T|>0$, including the one-element tag alphabet when $m=0$.
-- source:
--   Key recycling in authentication, arXiv:1202.1229v3, PDF p. 4, Section 2.3, Eqs. (4)–(5)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P41

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P41

open QAlgorithms.Papers.Independent.Bridge50.P44 (xorWord verifyTag)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.4--5, Definition 2 and Eqs.(4)--(5): OTP extension is ASU2;
its tags are uniform for every fixed hash key; the conditional pair bound holds.
No nontrivial-message assumption is needed for these algebraic identities. -/
theorem hash_otp {K X : Type*} [Fintype K] [Nonempty K] {m : ℕ}
    (h : K → X → Tag m) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hh : IsAXU2 h epsilon) :
    IsASU2 (fun seed : K × Tag m => paddedTag h seed.1 seed.2) epsilon ∧
    (∀ k x t, uniformProbability (fun pad => paddedTag h k pad x = t) =
      1 / (Fintype.card (Tag m) : ℝ)) ∧
    (∀ x y, x ≠ y → ∀ a b,
      uniformProbability (fun seed : K × Tag m =>
        paddedTag h seed.1 seed.2 x = a ∧ paddedTag h seed.1 seed.2 y = b) /
      uniformProbability (fun seed : K × Tag m => paddedTag h seed.1 seed.2 x = a)
        ≤ epsilon) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P41

end
