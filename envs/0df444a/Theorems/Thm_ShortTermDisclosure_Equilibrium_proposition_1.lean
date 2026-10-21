-- Prove2me | Theorems.Thm_ShortTermDisclosure_Equilibrium_proposition_1
-- name    : ShortTermDisclosure.Equilibrium.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:43:33.695766+00:00
-- url     : https://prove2.me/theorems/30d31199-0502-406e-8a53-49331b175ea4
-- title:
--   Proposition 1 — disclosure equilibrium regimes
-- statement:
--   Under $\bar\mu/2<\underline v<\bar v<\bar\mu$ and $0<p<1$, there is a threshold $\lambda^*\in(0,1)$, chosen before the shareholder's $\eta\in[0,1]$, and an equilibrium exists for every such $\eta$. Write $\lambda=\eta/(2-\eta)$. Every equilibrium has these disclosure regions:
--
--   1. At $\lambda=0$, the informed manager discloses every value in $[\underline v,\bar v]$.
--   2. For $0<\lambda\le\lambda^*$, he withholds exactly on $(v_1,v_2)$, where $v_2=E[v\mid ND]$ and $v_1=\frac{1+\lambda}{1-\lambda}v_2-\frac{2\lambda}{1-\lambda}\bar\mu$.
--   3. For $\lambda^*<\lambda\le1$, he withholds exactly on $[\underline v,v')$, where $v'=E[v\mid ND]$.
--
--   $$E[v\mid ND]=\frac{p\Pr(v\in ND)E[v\mid v\in ND]+(1-p)E[v]}{p\Pr(v\in ND)+1-p},\qquad\mu^*(d)=(1+\lambda)E[v\mid d]-\lambda\bar\mu.$$
--
--   The belief and shareholder responses are thus Bayes-consistent. **Formalization Note** The statement gives existence and the shape of every equilibrium. Manager indifference is resolved toward disclosure.
-- source:
--   Jia & Menon, Shareholder short-termism, corporate control and voluntary disclosure, authors' manuscript (SSRN 4029096, Minerva Access copy), p. 18 (PDF 21), Proposition 1 and (9)–(11)

import Mathlib
import Definitions.Def_ShortTermDisclosure_Equilibrium_Model

namespace ShortTermDisclosure.Equilibrium

theorem proposition_1 (P : Params) (hP : P.Standing) :
    ∃ lamStar : ℝ, 0 < lamStar ∧ lamStar < 1 ∧
    ∀ η : ℝ, 0 ≤ η → η ≤ 1 →
      (∃ E : Profile, IsEquilibrium P η E) ∧
      ∀ E : Profile, IsEquilibrium P η E →
        E.tN = (1 + lam η) * E.N - lam η * P.muhi ∧
        (∀ v ∈ Set.Icc P.vlo P.vhi,
          E.tD v = (1 + lam η) * v - lam η * P.muhi) ∧
        (lam η = 0 → E.D = Set.Icc P.vlo P.vhi) ∧
        (0 < lam η → lam η ≤ lamStar →
          P.vlo ≤ (1 + lam η) / (1 - lam η) * E.N -
            2 * lam η / (1 - lam η) * P.muhi ∧
          (1 + lam η) / (1 - lam η) * E.N -
            2 * lam η / (1 - lam η) * P.muhi < E.N ∧
          E.N ≤ P.vhi ∧
          Set.Icc P.vlo P.vhi \ E.D =
            Set.Ioo ((1 + lam η) / (1 - lam η) * E.N -
              2 * lam η / (1 - lam η) * P.muhi) E.N) ∧
        (lamStar < lam η →
          P.vlo < E.N ∧ E.N ≤ P.vhi ∧
          Set.Icc P.vlo P.vhi \ E.D = Set.Ico P.vlo E.N) := by sorry

end ShortTermDisclosure.Equilibrium
