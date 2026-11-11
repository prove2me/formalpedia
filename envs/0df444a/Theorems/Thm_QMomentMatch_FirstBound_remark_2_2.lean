-- Prove2me | Theorems.Thm_QMomentMatch_FirstBound_remark_2_2
-- name    : QMomentMatch.FirstBound.remark_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T19:00:54.540411+00:00
-- url     : https://prove2.me/theorems/96ef9440-7c23-490d-a9be-a095a4b48651
-- title:
--   Remark 2.2, eq. (5) — $\Pr_{\Pi_N}[\mathcal A^f=1]=\mathbb E_{z\sim\pi^{\otimes m}}[h(z)]$
-- statement:
--   Let $A\ge1$, $N\ge1$, $S=\{0\}\cup[A]$ and $m=\lfloor N/2\rfloor$. Let $X$ be positive frequency statistics supported on $[A]$, let $\pi$ be the law of its mean-one statistics $Z$, and let $\Pi_N$ be the induced input distribution of Definition 2.1. For $z\in S^m$ let $\mathbf c(z)$ be the frequency vector of step 2 of Definition 2.1. Then for every quantum query algorithm $\mathcal A$,
--   $$\Pr_{f\sim\Pi_N}[\mathcal A^f=1]=\mathbb E_{z\sim\pi^{\otimes m}}[h(z)],\qquad h(z)=\Pr_{f\sim\mathcal D_{\mathbf c(z)}}[\mathcal A^f=1].$$
--
--   This identity lets the proof of Theorem 2.5 replace the input law by the product law $\pi^{\otimes m}$ of the multiplicities and analyse the symmetric function $h$ with a hybrid argument over the $m$ coordinates.
--
--   **Formalization Note** Algorithms are `QAlgorithms.QueryAlg (Fin N) (ZMod N) W T` with any finite workspace `W` and any number of queries `T`, with output map `out` on computational-basis outcomes.
--
--   Differences from the source:
--   - reading: "positive frequency statistics $X$ supported on $[A]$" → any probability vector on $\{1,\dots,A\}$; reason: only the law of $X$ enters Definition 2.1.
--   - encoding: $f:[N]\to[N]$ with oracle $|i,y\rangle\mapsto|i,y+f(i)\bmod N\rangle$ → `f : Fin N → ZMod N` with `xorOracle f`; reason: relabel the domain 0-based and each label $j$ as $j\bmod N$; the oracle is then literally the same unitary.
--   - encoding: frequency vector $\mathbf c(z)$ → the multiset of its entries; reason: $\mathcal D_{\mathbf c}$ depends on $\mathbf c$ only up to permutation.
--   - encoding: "every algorithm with query access to $f$" → every `QueryAlg` with any finite workspace, any $T$, and any Boolean map of the final basis measurement; reason: a general two-outcome final measurement folds into $U_T$, so this is the full class.
-- source:
--   Chandrima Kayal, Frédéric Magniez, Sayantan Sen, Dániel Szabó, STOC 2027 submission #564 (October 2026), Remark 2.2, eq. (5), p. 12

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QMomentMatch_FirstBound_Basic
import Definitions.Def_QMomentMatch_FirstBound_InducedDist

namespace QMomentMatch.FirstBound

open QAlgorithms

/-- Remark 2.2, eq. (5), p. 12: `Pr_{f ∼ Π_N}[A^f = 1] = E_{z ∼ π^{⊗m}}[h(z)]` with
`h(z) = Pr_{f ∼ D_{c(z)}}[A^f = 1]`, `m = ⌊N/2⌋`, `π` the law of `Z`. -/
theorem remark_2_2 (A N : ℕ) [NeZero N] (hA : 1 ≤ A) (X : Fin (A + 1) → ℝ)
    (hX : IsPosFreqStat X) (W : Type*) [Fintype W] [DecidableEq W] (T : ℕ)
    (alg : QueryAlg (Fin N) (ZMod N) W T) (out : (Fin N × ZMod N) × W → Bool) :
    probAccept (inducedDist X N) alg out =
      prodExp (meanOne X) fun z : Fin (N / 2) → Fin (A + 1) => hAcc alg out z := by sorry

end QMomentMatch.FirstBound
