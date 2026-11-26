-- Prove2me | Theorems.Thm_Rank2Sha_curve389a1_kuriharaNumber_ne_zero
-- name    : Rank2Sha.curve389a1_kuriharaNumber_ne_zero
-- status  : Open
-- author  : @barindersbanwait
-- created : 2026-11-26T14:28:02.525911+00:00
-- url     : https://prove2.me/theorems/982f38e5-591e-4b46-b52c-912c95900109
-- title:
--   Nonzero Kurihara numbers of 389a1 for almost all $p$ (K2)
-- statement:
--   Let $E$ be the elliptic curve $y^2 + y = x^3 + x^2 - 2x$ over $\mathbb{Q}$ (LMFDB 389.a1), with the basis $P_1 = (0,0)$, $P_2 = (-1,1)$ of $E(\mathbb{Q})$. For a prime $p$, a **Kolyvagin prime** for $p$ is a prime $l \ne 389$ with $l \equiv 1 \pmod p$ such that $E(\mathbb{F}_l)[p]$ is cyclic of order $p$.
--
--   For distinct Kolyvagin primes $l_1, l_2$ for $p$, the **Kurihara number** is
--
--   $$
--   \delta_{l_1 l_2} = \sum_{a \in (\mathbb{Z}/l_1l_2\mathbb{Z})^\times} \Big[ \frac{a}{l_1 l_2} \Big]^+ \lambda_{l_1}(a)\, \lambda_{l_2}(a) \in \mathbb{F}_p ,
--   $$
--
--   where $[r]^+$ is the plus modular symbol of $E$ normalised by $\Omega^+ = \int_{E(\mathbb{R})}|\omega|$ and $\lambda_l$ is the discrete logarithm modulo $l$ to the least primitive root, reduced modulo $p$.
--
--   The statement: there is a finite set $S_0$ of primes such that for every prime $p \notin S_0$ there are distinct Kolyvagin primes $l_1, l_2$ for $p$ with
--
--   $$
--   \delta_{l_1 l_2} \ne 0 \quad \text{in } \mathbb{F}_p .
--   $$
--
--   Status: open. It follows from the identity $\delta_{l_1l_2} = M(l_1,l_2)$ for almost all $p$ (`Rank2Sha.curve389a1_kurihara_mazurTate`, open) and the existence of Kolyvagin primes with $M(l_1,l_2) \ne 0$ (`Rank2Sha.curve389a1_tameDiscriminant_ne_zero`), where $M$ is the tame discriminant of the definition `Rank2Sha_Kurihara389`. By C.-H. Kim's Theorem 1.8 (Amer. J. Math. 148 (2026); numbering of arXiv:2203.12159v6), for a prime $p \ge 5$ with surjective mod $p$ representation and Manin constant prime to $p$, one pair with $\delta_{l_1l_2} \ne 0$ gives $\mathrm{Sel}(\mathbb{Q}, E[p^\infty]) \cong (\mathbb{Q}_p/\mathbb{Z}_p)^2$, hence $\text{Ш}(E/\mathbb{Q})[p] = 0$. So the statement implies $\text{Ш}(E/\mathbb{Q})[p] = 0$ for all but finitely many $p$; that implication needs Selmer groups and is not formalized here.
--
--   **Formalization Note** Primality of $p$ is an instance argument `[Fact p.Prime]`; the primality of $l_1, l_2$ is part of the existential, as witnesses of type `Fact _.Prime`. The objects are those of the definition `Rank2Sha_Kurihara389`; their agreement with the objects of the literature is a computation recorded in the definitions `Rank2Sha_PlusSymbol389` and `Rank2Sha_TatePairing`.
-- source:
--   C.-H. Kim, The structure of Selmer groups and the Iwasawa main conjecture for elliptic curves, Amer. J. Math. 148 (2026), arXiv:2203.12159v6, Theorem 1.8 ; B. Mazur, K. Rubin, Kolyvagin systems, Mem. Amer. Math. Soc. 168 (2004), no. 799, Proposition 3.6.2 ; M. Kurihara, Münster J. Math. 7 (2014)

import Mathlib
import Definitions.Def_Rank2Sha_Kurihara389

namespace Rank2Sha
theorem curve389a1_kuriharaNumber_ne_zero :
    ∃ S₀ : Finset ℕ, ∀ (p : ℕ) [Fact p.Prime], p ∉ S₀ →
      ∃ (l₁ l₂ : ℕ) (_ : Fact l₁.Prime) (_ : Fact l₂.Prime), l₁ ≠ l₂ ∧
        IsKolyvaginPrime p l₁ ∧ IsKolyvaginPrime p l₂ ∧
          kuriharaNumber389 p l₁ l₂ ≠ 0 := by sorry
end Rank2Sha
