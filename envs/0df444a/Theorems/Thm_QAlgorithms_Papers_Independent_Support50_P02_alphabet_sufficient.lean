-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P02_alphabet_sufficient
-- name    : QAlgorithms.Papers.Independent.Support50.P02.alphabet_sufficient
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:21:22.120026+00:00
-- url     : https://prove2.me/theorems/be99577b-11c1-4813-ac0d-b2776abb18d0
-- title:
--   §7.5: alphabet cardinality sufficiency
-- statement:
--   Let $\mathcal N:A'B'\to C$ be a completely positive, trace-preserving channel between finite, positive-dimensional complex quantum registers. Alice and Bob control separate inputs. Codes use independent sender preparations, local encoders, one joint memoryless channel and one joint decoder, with external references untouched and no free shared resources. Fidelity is squared Uhlmann fidelity, trace distance is the full trace norm, and entropies are in bits. Write $CQ(\mathcal N)$ and $Q(\mathcal N)$ for the closed operational classical–quantum and quantum–quantum capacity regions, using joint output fidelity and nonnegative rates.
--
--   For a pure ensemble $\{p_x,\phi_x^{A'}\}$ and an independent pure state $\Psi^{BB'}$, let $\sigma^{XBC}=\sum_xp_x|x\rangle\langle x|\otimes(\operatorname{id}_B\otimes\mathcal N)(\phi_x\otimes\Psi)$. Write $H$ for von Neumann entropy in bits, $I(U;V)=H(U)+H(V)-H(UV)$, and $I_c(U\rangle V)=H(V)-H(UV)$.
--
--   Put $L=\min\{|A'|,|C|\}^2+1$. Every such ensemble can be replaced by a pure ensemble on at most $L$ letters, keeping Bob's pure pair fixed and preserving both $I(X;C)$ and $I_c(B\rangle CX)$. If $|A'|\le|C|$, the average Alice input can also be preserved; otherwise the average Charlie output can be preserved. Consequently,
--   $$CQ^{(1)}(\mathcal N;\text{all finite alphabets})=CQ^{(1)}(\mathcal N;|X|\le L).$$
--   This makes the alphabet optimization finite-dimensional while retaining the same one-use region.
--
--   **Formalization Note** The replacement may use new pure states. The corrected connected domain is the image of all pure inputs, rather than a fixed finite family.
-- source:
--   Capacity Theorems for Quantum Multiple Access Channels: Classical-Quantum and Quantum-Quantum Capacity Regions, arXiv:quant-ph/0501045v3, PDF p. 36, §7.5: alphabet cardinality sufficiency

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P02

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Support50.P02

open QAlgorithms.Papers.Independent.Information100.P67
  (squaredFidelity receiverChannel complementaryChannel IsDegradable)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

open QAlgorithms.Papers.Independent.Dependency50.P19 (epr)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C E R S I J : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype E] [DecidableEq E]

variable [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Alphabet sufficiency, §7.5, PDF p.36, also Theorem 1 p.8.
Corrected domain: replacement points may be NEW pure states from the continuous
image of ALL pure inputs. The printed finite-family simplex argument does not
justify same-support sparsification. The smaller-input branch preserves average
INPUT; the smaller-output branch preserves average output. Bob's pure pair stays fixed. -/
theorem alphabet_sufficient [Nonempty A] [Nonempty B] [Nonempty C]
    (N : Superop (A × B) C) (hN : IsChannel N) :
    cqOne N none = cqOne N (some (min (Fintype.card A) (Fintype.card C) ^ 2 + 1)) ∧
    (∀ D : CQMacData A B, ∃ P : PureEnsemble A,
      P.count ≤ min (Fintype.card A) (Fintype.card C) ^ 2 + 1 ∧
      let Dnew : CQMacData A B := { D with ensemble := P }
      Dnew.classical N = D.classical N ∧
      Dnew.conditionalCoherent N = D.conditionalCoherent N ∧
      (if Fintype.card A ≤ Fintype.card C then pureEnsembleAverage P = pureEnsembleAverage D.ensemble
       else traceLeft (Dnew.averageOutput N) = traceLeft (D.averageOutput N))) := by sorry

end QAlgorithms.Papers.Independent.Support50.P02

end
