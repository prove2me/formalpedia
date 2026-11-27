-- Prove2me | Theorems.Thm_Rank2Sha_curve389a1_sha_no_p_torsion_of_kuriharaNumber_ne_zero
-- name    : Rank2Sha.curve389a1_sha_no_p_torsion_of_kuriharaNumber_ne_zero
-- status  : Open
-- author  : @barindersbanwait
-- created : 2026-11-26T23:49:11.785449+00:00
-- url     : https://prove2.me/theorems/fe3d8c7c-7d04-4ed7-aa3e-0c04cb37c7c6
-- title:
--   A nonzero Kurihara number of 389a1 at $p$ gives $\text{Ш}(E/\mathbb{Q})[p] = 0$, for almost all $p$
-- statement:
--   Let $E$ be the elliptic curve $y^2 + y = x^3 + x^2 - 2x$ over $\mathbb{Q}$ (LMFDB 389.a1) and $\text{Ш}(E/\mathbb{Q})$ its Shafarevich–Tate group. For a prime $p$, a **Kolyvagin prime** for $p$ is a prime $l \ne 389$ with $l \equiv 1 \pmod p$ such that $E(\mathbb{F}_l)[p]$ is cyclic of order $p$.
--
--   For distinct Kolyvagin primes $l_1, l_2$ for $p$, the **Kurihara number** is
--
--   $$
--   \delta_{l_1 l_2} = \sum_{a \in (\mathbb{Z}/l_1l_2\mathbb{Z})^\times} \Big[ \frac{a}{l_1 l_2} \Big]^+ \lambda_{l_1}(a)\, \lambda_{l_2}(a) \in \mathbb{F}_p ,
--   $$
--
--   where $[r]^+$ is the plus modular symbol of $E$ normalised by $\Omega^+ = \int_{E(\mathbb{R})}|\omega|$ and $\lambda_l$ is the discrete logarithm modulo $l$ to the least primitive root, reduced modulo $p$.
--
--   The statement: there is a finite set $S_1$ of primes such that for every prime $p \notin S_1$ and all distinct Kolyvagin primes $l_1, l_2$ for $p$,
--
--   $$
--   \delta_{l_1 l_2} \ne 0 \ \text{ in } \mathbb{F}_p \quad \Longrightarrow \quad \text{Ш}(E/\mathbb{Q})[p] = 0 .
--   $$
--
--   Status: open, not formalized. It is a consequence of C.-H. Kim, Theorem 1.8 with Proposition 3.14 (Amer. J. Math. 148 (2026); numbering of arXiv:2203.12159v6), together with the rank bound $\operatorname{rank} E(\mathbb{Q}) \ge 2$ and the descent sequence. Kim's theorem applies at primes $p \ge 5$ at which the mod $p$ representation of $E$ is surjective and the Manin constant is prime to $p$; for this curve one pair with $\delta_{l_1l_2} \ne 0$ then gives $\mathrm{Sel}(\mathbb{Q}, E[p^\infty]) \cong (\mathbb{Q}_p/\mathbb{Z}_p)^2$. Those hypotheses fail at only finitely many $p$, since $E$ has no complex multiplication (Serre, 1972). The statement asks only for some finite set $S_1$.
--
--   Kim's paper computes $\delta_{41 \cdot 61} \ne 0$ in $\mathbb{F}_5$ for this curve; the definition `Rank2Sha_Kurihara389` gives $\delta_{41\cdot 61} = 2$ in $\mathbb{F}_5$.
--
--   With `Rank2Sha.curve389a1_kuriharaNumber_ne_zero` (K2) this statement gives `Rank2Sha.curve389a1_sha_no_p_torsion_almost_all`.
--
--   **Formalization Note** Primality of $p$, $l_1$, $l_2$ is an instance argument `[Fact _.Prime]`. $\text{Ш}(E/\mathbb{Q})$ is `curve389a1.tateShafarevich` (definition `Rank2Sha_TateShafarevich`), and $\text{Ш}(E/\mathbb{Q})[p] = 0$ is written as: every $x$ with $p \cdot x = 0$ is $0$. The Kurihara number and the Kolyvagin primes are those of the definition `Rank2Sha_Kurihara389`; their agreement with the objects of the literature is a computation recorded in the definitions `Rank2Sha_PlusSymbol389` and `Rank2Sha_TatePairing`, not a proof.
-- source:
--   C.-H. Kim, The structure of Selmer groups and the Iwasawa main conjecture for elliptic curves, Amer. J. Math. 148 (2026), arXiv:2203.12159v6, Theorem 1.8 and Proposition 3.14 ; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., Graduate Texts in Mathematics 106, Springer 2009, https://doi.org/10.1007/978-0-387-09494-6, Chapter X, Section 4 (descent sequence) ; J.-P. Serre, Propriétés galoisiennes des points d'ordre fini des courbes elliptiques, Invent. Math. 15 (1972), 259-331

import Mathlib
import Definitions.Def_Rank2Sha_Kurihara389
import Definitions.Def_Rank2Sha_TateShafarevich

namespace Rank2Sha
theorem curve389a1_sha_no_p_torsion_of_kuriharaNumber_ne_zero :
    ∃ S₁ : Finset ℕ, ∀ (p : ℕ) [Fact p.Prime], p ∉ S₁ →
      ∀ (l₁ l₂ : ℕ) [Fact l₁.Prime] [Fact l₂.Prime], l₁ ≠ l₂ →
        IsKolyvaginPrime p l₁ → IsKolyvaginPrime p l₂ → kuriharaNumber389 p l₁ l₂ ≠ 0 →
          ∀ x : curve389a1.tateShafarevich, p • x = 0 → x = 0 := by sorry
end Rank2Sha
