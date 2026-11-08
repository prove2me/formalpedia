-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P16_measurableFunctionSheaf_flasque_of_secondCountable
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P16.measurableFunctionSheaf_flasque_of_secondCountable
-- status  : Proved
-- author  : @shivm
-- created : 2026-11-07T14:17:59.698343+00:00
-- url     : https://prove2.me/theorems/27952cb4-bedd-4e6d-af07-0a29fd6a9601
-- title:
--   Second countability makes the sheaf of locally Borel functions flasque
-- statement:
--   Let \(X\) be a second-countable topological space and \(A\) a nonempty topological space. Write \(\mathcal M_A\) for the sheaf obtained by sheafifying the local predicate of pointwise Borel-measurable \(A\)-valued functions on open subsets of \(X\). Then \(\mathcal M_A\) is flasque: for every inclusion of open sets \(U\subseteq V\subseteq X\),
--   \[
--   \Gamma(V,\mathcal M_A)\longrightarrow\Gamma(U,\mathcal M_A)
--   \quad\text{is surjective}.
--   \]
--   Thus every section on an open subset extends to every larger open subset. The result requires no group, local-compactness, Hausdorff, or Lie-group structure. It supplies the measurable-function extension theorem on every finite power of a second-countable topological group, with any nonempty topological coefficient space.
-- source:
--   Corrected second-countable form of the pointwise Borel/sheafification statement attached to Brylinski, Differentiable Cohomology of Gauge Groups, Lemma 2.5 (arXiv:math/0011069v1, p.11). Uses the unchanged canonical Prove2Me definitions.

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P16
import Mathlib.Topology.Compactness.Lindelof

universe u w

theorem QAlgorithms.Papers.Independent.Intakenext100.P16.measurableFunctionSheaf_flasque_of_secondCountable (X : TopCat.{u}) [SecondCountableTopology X]
    (A : Type w) [TopologicalSpace A] [Nonempty A] :
    TopCat.Sheaf.IsFlasque
      (QAlgorithms.Papers.Independent.Intakenext100.P16.measurableFunctionSheaf X A) := by sorry
