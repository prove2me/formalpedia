-- Prove2me | Theorems.Thm_ShuffleDecoys_Hierarchy_b9_dependent_upper
-- name    : ShuffleDecoys.Hierarchy.b9_dependent_upper
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:23:21.984197+00:00
-- url     : https://prove2.me/theorems/f0fefa27-370d-4153-aabf-7ce1570c0d12
-- title:
--   Appendix B.9, proof of Theorem B.1 — the random n-set mechanism leaks ≤ log(d/n) (n < d); the fixed-multiset mechanism leaks 0 (n ≥ d)
-- statement:
--   Let $d,n\ge2$.
--
--   *Case $n<d$.* Given $M=m$, choose an $n$-element set $A\subseteq[d]$ uniformly among those containing $m$, and release a uniformly random ordering $Z$ of $A$. This mechanism does not depend on the prior, and for every prior $P$
--   $$I_P(M;Z)\ \le\ \log(d/n).$$
--
--   *Case $n\ge d$.* Fix a multiset of size $n$ containing every symbol of $[d]$; on input $m$ use the multiset with one occurrence of $m$ removed as the decoys. The release is a uniformly random ordering of the fixed multiset whatever $m$ is, and
--   $$I_P(M;Z)=0\quad\text{for every prior }P.$$
--
--   Differences from the source:
--   - encoding: "choose $A\ni m$ uniformly, release a uniform ordering of $A$" → decoys $A\setminus\{m\}$ listed in increasing order, i.e. a kernel with mass $\binom{d-1}{n-1}^{-1}$ on each strictly increasing $(n-1)$-tuple avoiding $m$, followed by the uniform shuffle of all $n$ positions; reason: the shuffle of $(m,A\setminus\{m\})$ is a uniform ordering of $A$, and $A\setminus\{m\}$ is a uniform $(n-1)$-subset of $[d]\setminus\{m\}$.
--   - encoding: the fixed multiset → its count vector $c$ with $c(y)\ge1$ and $\sum_yc(y)=n$; "the multiset minus one $m$ as decoys" → any deterministic decoy tuple $h_m$ whose histogram plus $e_m$ is $c$; reason: the order in which the decoys are listed is erased by the shuffle, and every listing is covered.
--   - reading: the chain $I_P(M;Z)=I_P(M;A)=H_P(A)-H_P(A\mid M)\le\log\binom dn-\log\binom{d-1}{n-1}$ → only its conclusion; reason: the intermediate steps are the proof.
-- source:
--   Su, Cheng, Wang, The Information-Theoretic Limits of Hiding Among Decoys in the Shuffle Model, STOC 2027 submission (manuscript sha256 445baceb…), p. 47, Appendix B.9, proof of Theorem B.1, 'Exact characterization of message-dependent decoys', upper bound

import Mathlib
import Definitions.Def_ShuffleDecoys_Hierarchy_Info
import Definitions.Def_ShuffleDecoys_Hierarchy_Model

open scoped ENNReal

namespace ShuffleDecoys.Hierarchy

/-- Appendix B.9, proof of Theorem B.1, message-dependent upper bound. If `n < d`: the mechanism
that, given `M = m`, picks an `n`-set `A ∋ m` uniformly (decoys `A \ {m}` listed in increasing
order, so the shuffle releases a uniform ordering of `A`) leaks `I_P(M; Z) ≤ log(d/n)` for every
prior. If `n ≥ d`: fixing a size-`n` multiset `c` containing every symbol and using `c` minus
one copy of `m` as decoys gives zero leakage for every prior. -/
theorem b9_dependent_upper (d n : ℕ) (hd : 2 ≤ d) (hn : 2 ≤ n) :
    (n < d → ∀ R : DecoyKernel (Fin d) n,
      (∀ m h, R m h =
        if (∀ i j, i < j → h i < h j) ∧ (∀ i, h i ≠ m) then
          ((Nat.choose (d - 1) (n - 1) : ℝ≥0∞))⁻¹ else 0) →
      ∀ P : PMF (Fin d), leakage P R ≤ ENNReal.ofReal (Real.log ((d : ℝ) / n))) ∧
    (d ≤ n → ∀ c : Fin d → ℕ, (∀ y, 1 ≤ c y) → ∑ y, c y = n →
      ∀ h : Fin d → Fin (n - 1) → Fin d,
        (∀ m y, (Finset.univ.filter fun i => h m i = y).card + (if y = m then 1 else 0) = c y) →
        ∀ P : PMF (Fin d), leakage P (fun m => PMF.pure (h m)) = 0) := by sorry

end ShuffleDecoys.Hierarchy
