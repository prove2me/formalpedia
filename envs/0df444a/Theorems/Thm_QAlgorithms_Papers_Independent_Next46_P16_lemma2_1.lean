-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P16_lemma2_1
-- name    : QAlgorithms.Papers.Independent.Next46.P16.lemma2_1
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:00:52.729987+00:00
-- url     : https://prove2.me/theorems/13cdb1f7-8174-4fb7-a640-40179c149c74
-- title:
--   Schwartz vectors characterized by Hilbert-bounded test forms
-- statement:
--   Fix a positive integer $N$, and let $\mathcal H=L^2(\mathbb R^N,dq)$ with inner product conjugate-linear in its first argument. Let $Q_j$ multiply by $q_j$, and let $P_j=-i\partial_{q_j}$ on Schwartz functions. For multi-indices $\alpha,\beta\in\mathbb N_0^N$, set
--   $$
--   b_{\alpha,\beta}(v)=\sup_{\psi\in\mathcal S(\mathbb R^N),\ \|\psi\|_2\le1}|\langle P^\beta Q^\alpha\psi,v\rangle|.
--   $$
--   An $L^2$ class $v$ has a Schwartz representative if and only if every set in these suprema is bounded above. For every Schwartz function $f$,
--   $$
--   b_{\alpha,\beta}([f])=\|Q^\alpha P^\beta f\|_2.
--   $$
--   This characterizes Schwartz vectors without assuming differentiability of an arbitrary $L^2$ representative.
-- source:
--   Schwartz operators, arXiv:1503.04086v1, PDF p. 4, Lemma 2.1

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P16

noncomputable section

open MeasureTheory Filter

open QAlgorithms.Papers.Independent.Claimed50.P10 (Configuration)

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass)

open scoped BigOperators ENNReal ComplexOrder

namespace QAlgorithms.Papers.Independent.Next46.P16

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P16.canonicalComplexCalculus

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P16.canonicalRealCalculus

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P16.canonicalRealNonUnitalCalculus

/-- Lemma 2.1, PDF p.4, (9)--(11): boundedness of every Hilbert-space test
functional characterizes Schwartz representatives, and its bound equals (9). -/
theorem lemma2_1 (n : ℕ) (hn : 0 < n) :
    (∀ v : CanonicalHilbert n, IsSchwartzVector v ↔
      ∀ a b : MultiIndex n, BddAbove (vectorFormValues v a b)) ∧
    (∀ (f : Schwartz n) (a b : MultiIndex n),
      vectorFormBound (schwartzToHilbert f) a b =
        ‖schwartzToHilbert (vectorAction a b f)‖) := by sorry

end QAlgorithms.Papers.Independent.Next46.P16

end
