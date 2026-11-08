-- Prove2me | Theorems.Thm_QuadraticRE_proposition_4_4_step_1
-- name    : QuadraticRE.proposition_4_4_step_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:14:03.140361+00:00
-- url     : https://prove2.me/theorems/3747e2da-061b-40d9-bf0e-c1dd498f5a60
-- title:
--   Proposition 4.4, Step 1 — sampling from selected shares
-- statement:
--   Fix $j\ge0$, $h\ge3$, $(a,b,c,d)$ and $y=abc+d$. Sample $\mathbf a=\mathrm{Sh}^j_A(a;\theta_A)$ and $\mathbf c=\mathrm{Sh}^j_C(c;\theta_C)$ with independent uniform masks and, independently, a leaf vector $\mathbf y$ uniform on $P_y$; generate every row of every $Q_i$ by $\mathrm{RowSamp}(y_i,c_i,a_i)$ with fresh bits. Then:
--
--   1. the resulting list of matrices has exactly the law of $E_{j,h}(a,b,c,d;R)$;
--   2. there is a single map $G$, depending only on $j,h$, that produces the matrices from $\mathbf y$, the selected shares $\mathbf c[S_C]$ and $\mathbf a[S_A]$ and the fresh bits, for all leaf vectors; and $S_A$ is computed from $\mathbf y$ and $\mathbf c[S_C]$ alone.
--
--   This identifies the shares on which the distribution of the encoding depends.
--
--   Differences from the source:
--   - encoding: fresh independent randomness for every call of RowSamp → an array of uniform bits indexed by leaf, row and (U, V, T); reason: the same independent uniform bits
--   - reading: given y, the matrices can be generated using only the selected shares → one map G, fixed before the input, from (y, c[S_C], a[S_A], fresh bits) to the matrices, with S_A computed from (y, c[S_C]); reason: "generated using only" is a factorization through these data
--   - generalization: the factorization for the sampled sharings → the factorization for all leaf vectors (a_i), (c_i), y; reason: it holds pointwise, so in particular on the sampled ones
-- source:
--   Orsini, Patra, From Degree Three to Degree Two: Statistical Randomized Encodings for All Functions, STOC 2027 submission manuscript (sha256 0c94deae…), Lemma (Sampling from selected shares; Proposition 4.4, Step 1), p.9; proof of Proposition 4.4, Step 1, pp.20–21

import Mathlib
import Definitions.Def_QuadraticRE_rowSamp

namespace QuadraticRE

/-- "Lemma (Sampling from selected shares; Proposition 4.4, Step 1)" of Orsini, Patra, *From Degree Three to Degree Two*, STOC 2027 submission manuscript (sha256 0c94deae…), stated p.9, proved
pp.20–21. First clause: sampling `y` uniformly from `P_y`, the two sharings independently, and every
row by `RowSamp` gives exactly the law of `E_{j,h}(a, b, c, d; R)`. Second clause ("In particular"): one
map `G`, fixed before all the data, generates the matrices from `y`, `c[S_C]`, `a[S_A]` and the fresh
bits, where `S_A` is itself computed from `y` and `c[S_C]`.

**Formalization Note.** `RowSamp` is (6), so the identity (5) is proved and not assumed. -/
theorem proposition_4_4_step_1 (j h : ℕ) (hh : 3 ≤ h) :
    (∀ a b c d : F2,
      law (fun ω : Py j (a * b * c + d) × (Fin (maskLen .A j) → F2) × (Fin (maskLen .C j) → F2) ×
            Coins j h =>
          sampleFrom (Sh .A j a ω.2.1) (Sh .C j c ω.2.2.1) ω.1.val ω.2.2.2)
        = law (encE j h a b c d)) ∧
    ∃ G : ∀ (η : Fin (4 ^ j) → F2) (cS : selC η → F2), (selAOf η cS → F2) → Coins j h → Encoded j h,
      ∀ (aL cL η : Fin (4 ^ j) → F2) (ω : Coins j h),
        selAOf η ((selC η).restrict cL) = selA cL η ∧
        sampleFrom aL cL η ω =
          G η ((selC η).restrict cL) ((selAOf η ((selC η).restrict cL)).restrict aL) ω := by sorry

end QuadraticRE
