-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P49_rowColumnRecovery
-- name    : QAlgorithms.Papers.Independent.Extend50.P49.rowColumnRecovery
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:25:13.809441+00:00
-- url     : https://prove2.me/theorems/2993c0de-892b-43a8-8fd0-d38290eb45f4
-- title:
--   Recovery of actual row and column indices in both source regimes
-- statement:
--   In either source construction fix finite alphabets, a broadcast channel, a normalized joint auxiliary law, and a deterministic auxiliary-to-input map. Let $M_i>0$ be integer message counts, $R_i=\log_2M_i$, and let $a,b,c$ be the actual finite smooth information values. Take $0<\varepsilon_0<1$, $0<\varepsilon_\infty\le1/4$, and positive padding integers satisfying
--   $$R_1+r_1\le a-4L-1,\quad R_2+r_2\le b-4L-1,\quad r_1,r_2\ge L,\quad r_1+r_2=\lceil c+3L\rceil,\qquad L=\log_2(1/t).$$
--   Use the source tests on the actual induced states/distributions: in the quantum case, effects with acceptance at least $1-\varepsilon_0$ and product-state acceptance at most $2^{-a}$ and $2^{-b}$; in the classical case, sets with acceptance strictly greater than $1-\varepsilon_0$ and product-marginal masses at most these same thresholds. The smooth quantum quantities have strict feasible acceptance; the classical quantities have non-strict feasible mass.
--   For the quantum case assume $0<t\le1/40$ and $40t+16\varepsilon_0\le1$. For the classical case assume $0<t\le1/37$ and $37t+8\varepsilon_0\le1$. In each case there is ONE fixed codebook with strictly positive probability under the computed source rejection-sampling law, consisting of $M_12^{r_1}$ row symbols, $M_22^{r_2}$ column symbols, and retained cells. For each message pair the encoder uses the lexicographically first retained cell in its rectangle whose two local test-acceptance probabilities exceed $1-4\varepsilon_0$. A missing cell counts as failure. The receivers recover the actual selected row and column indices with average joint failure bounded by
--   $$\begin{cases}40t+16\varepsilon_0,&\text{quantum case},\\37t+8\varepsilon_0,&\text{classical case}.\end{cases}$$
--   The average is over independent uniform messages and the actual channel output; the codebook and decoders are fixed before the messages. Quantum decoders are the source square-root measurements $S^{-1/2}\Lambda_kS^{-1/2}$, completed by adding the kernel projector of $S=\sum_k\Lambda_k$ to fixed index zero; both resulting local families are full POVMs. Classical decoders return the first index passing the source test, with fixed zero-index fallback. Distinct indices remain distinct when auxiliary symbols coincide. Recovering these indices also recovers their message bands.
-- source:
--   One-shot Marton inner bound for classical-quantum broadcast channel, arXiv:1410.3248v5, PDF p. 4, Unnumbered strengthening; pp.8-10,12-14

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P49

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P49

open QAlgorithms MeasureTheory Filter

open scoped BigOperators Matrix ComplexOrder Topology

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Unnumbered strengthening, PDF p.4, proved pp.8-10 and 12-14: each regime admits
one fixed codebook recovering the actual row/column pair on average, with the source's
40,16 and 37,8 constants. The existential codebook precedes unknown messages (averaged
in the computed error), and repeated symbols retain distinct indices. Quantum square-root
operators are completed on the kernel to genuine full POVMs. Each book has positive
weight in the source rejection-sampling experiment, so the witness is an actual
possible realization rather than an unrestricted retention array. -/
theorem rowColumnRecovery {X U V B C Y Z : Type}
    [Fintype X] [Fintype U] [Fintype V] [Fintype B] [Fintype C] [Fintype Y] [Fintype Z] :
    (∀ D : QuantumSetup X U V B C, 40 * D.tildeEpsilon + 16 * D.epsilon0 ≤ 1 →
      ∃ book : Codebook U V (D.M1 * 2 ^ D.r1) (D.M2 * 2 ^ D.r2),
        0 < bookWeight D.law D.c book ∧
        IsPOVM (fun k => completedPgm (fun j => testBlock D.test1 (book.row j)) k) ∧
        IsPOVM (fun l => completedPgm (fun j => testBlock D.test2 (book.column j)) l) ∧
        quantumIndexError D book ≤ 40 * D.tildeEpsilon + 16 * D.epsilon0) ∧
    (∀ D : ClassicalSetup X U V Y Z, 37 * D.tildeEpsilon + 8 * D.epsilon0 ≤ 1 →
      ∃ book : Codebook U V (D.M1 * 2 ^ D.r1) (D.M2 * 2 ^ D.r2),
        0 < bookWeight D.law D.c book ∧
        classicalIndexError D book ≤ 37 * D.tildeEpsilon + 8 * D.epsilon0) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P49

end
