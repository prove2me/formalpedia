-- Prove2me | Theorems.Thm_RandOrderCSP_lemma_10_14
-- name    : RandOrderCSP.lemma_10_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:10:40.147179+00:00
-- url     : https://prove2.me/theorems/8a34b4f6-9307-4b96-85bb-10832347bc8f
-- title:
--   Lemma 10.14 — neighborhood-to-exploration reduction
-- statement:
--   For every $k\ge2$, $D,r\in\mathbb N^+$, finite color set $\Gamma$ and $\varepsilon>0$, there are $R\in\mathbb N^+$ and a Markov kernel $Q:\mathcal E_{R,\Gamma}\to\Delta(\mathcal N_{D,r,\Gamma})$ such that for every finite nonempty $\Gamma$-colored $k$-uniform hypergraph $\Phi=(H,f)$,
--
--   $$\mathrm{tvd}\big(Q_*(\text{Rand-Exp-Type}_R(\Phi)),\ \text{Red-Nbhd-Type}_{D,r}(\Phi)\big)\le\varepsilon.$$
--
--   A deep random exploration of $\Phi$ thus simulates the neighbourhood of a random edge in a random regularization.
--
--   Differences from the source:
--   - encoding: a kernel into Δ(N_{D,r,Γ}) → a PMF on all rooted classes for each exploration type, with support in N_{D,r,Γ}; reason: the same objects; rooted classes form the ambient type
--   - encoding: tvd(P, P′) = ½∑|P(ω) − P′(ω)| over a finite set → a tsum over rooted classes; reason: both laws are finitely supported, so the sum is the finite one
-- source:
--   Singer, Tulsiani, Velusamy, A dichotomy theorem for approximating CSPs in random-order streams, STOC 2027 submission (manuscript sha256 3aca9d2f…), Lemma 10.14, p.55

import Mathlib
import Definitions.Def_RandOrderCSP_regularize
import Definitions.Def_RandOrderCSP_ExpTree

namespace RandOrderCSP

/-- **Lemma 10.14 (neighborhood-to-exploration reduction).** Singer, Tulsiani, Velusamy, *A dichotomy
theorem for approximating CSPs in random-order streams*, STOC 2027 submission (manuscript sha256
3aca9d2f…), Lemma 10.14, p.55.

**Formalization Note.** The Markov kernel is a `PMF` on rooted classes for each exploration type, with
support in `N_{D,r,Col}`. The pushforward is (3.4) and `tvd` is `½ ∑ |·|` (p.12). Both laws have finite
support, since `ℰ_{R,Col}` and `N_{D,r,Col}` are finite, so the `tsum`s are finite sums. -/
theorem lemma_10_14 {k : ℕ} (hk : 2 ≤ k) (D r : ℕ) (hD : 1 ≤ D) (hr : 1 ≤ r) (Col : Type) [Finite Col]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (R : ℕ) (Q : expTypes k R Col → PMF (RootedClass k Col)), 1 ≤ R ∧
      (∀ τ, (Q τ).support ⊆ nbhdTypes k D r Col) ∧
      ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [Nonempty E] (H : Hypergraph k V E)
        (f : E → Col),
        1 / 2 * ∑' N : RootedClass k Col,
            |∑' τ, expTypeLaw H f R τ * (Q τ N).toReal - redNbhdLaw H f D r N| ≤ ε := by sorry

end RandOrderCSP
