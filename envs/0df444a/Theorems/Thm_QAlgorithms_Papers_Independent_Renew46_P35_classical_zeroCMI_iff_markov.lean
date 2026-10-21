-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P35_classical_zeroCMI_iff_markov
-- name    : QAlgorithms.Papers.Independent.Renew46.P35.classical_zeroCMI_iff_markov
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:58:32.290354+00:00
-- url     : https://prove2.me/theorems/a450bd39-23fc-478d-b02b-d16936cfc43d
-- title:
--   Theorem 1: classical conditional independence and Markov factorization
-- statement:
--   Let $P$ be a joint PMF on discrete nonempty alphabets $A,B,C$, which may be infinite. Let $P_B,P_A,P_{AB}$ be its computed marginals. For $P_B(b)>0$ let $Q_b(a,c)=P(a,b,c)/P_B(b)$; for $P_A(a)>0$ let $K_a(b)=P_{AB}(a,b)/P_A(a)$. On null events choose arbitrary normalized conditional PMFs. Let $Q_b^A,Q_b^C$ be the two marginals of $Q_b$. Define conditional mutual information in bits by the extended nonnegative sum
--
--   $$I(A:C\mid B)=\sum_{b:P_B(b)>0}P_B(b)\,D(Q_b\Vert Q_b^A\otimes Q_b^C)/\ln 2.$$
--
--   Then $I(A:C\mid B)=0$ if and only if $Q_b=Q_b^A\otimes Q_b^C$ for every positive-probability $b$. This conditional independence holds if and only if, for all $a,b,c$,
--
--   $$P(a,b,c)=P_B(b)Q_b^A(a)Q_b^C(c)=P_A(a)K_a(b)Q_b^C(c).$$
--
--   These are the conditional independence and Markov factorizations reviewed by the source. Extended KL avoids undefined differences of infinite Shannon entropies.
-- source:
--   Structure of states which satisfy strong subadditivity of quantum entropy with equality, arXiv:quant-ph/0304007v2, PDF p. 2, Theorem 1: classical conditional independence and Markov factorization

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P35

noncomputable section

open scoped Matrix ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Renew46.P35

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted interfaces, inspected in the pinned library.

open QAlgorithms.Papers.Independent.Dependency50.P07
  (CQData ensembleMean ensembleInformation accessibleInformation)

open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)

open QAlgorithms.Papers.Independent.Dependency50.P35 (marginalAB marginalAC)

open QAlgorithms.Papers.Independent.Dependency50.P21 (petz)

open QAlgorithms.Papers.Independent.Information100.P06 (supportProjection)

open QAlgorithms.Papers.Independent.Information100.P22 (quantumMI)

/-- PDF pp.2–3, Theorem 1: zero CMI, conditional independence and both Markov factorizations.
Conditional PMFs at null events are arbitrary normalized completions. -/
theorem classical_zeroCMI_iff_markov {A B C : Type*} [Nonempty A] [Nonempty B] [Nonempty C]
    (p : PMF (A × (B × C))) (cond : B → PMF (A × C)) (ba : A → PMF B)
    (hcond : ∀ b, (p.map fun x => x.2.1) b ≠ 0 → ∀ a c,
      cond b (a, c) = p (a, (b, c)) / (p.map fun x => x.2.1) b)
    (hba : ∀ a, (p.map Prod.fst) a ≠ 0 → ∀ b,
      ba a b = (p.map fun x => (x.1, x.2.1)) (a, b) / (p.map Prod.fst) a) :
    let independent := ∀ b, (p.map fun x => x.2.1) b ≠ 0 →
      cond b = pmfProduct ((cond b).map Prod.fst) ((cond b).map Prod.snd)
    (classicalCMI p cond = 0 ↔ independent) ∧
    (independent ↔ ∀ a b c,
      p (a, (b, c)) = (p.map fun x => x.2.1) b *
        ((cond b).map Prod.fst) a * ((cond b).map Prod.snd) c ∧
      p (a, (b, c)) = (p.map Prod.fst) a * ba a b * ((cond b).map Prod.snd) c) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P35

end
